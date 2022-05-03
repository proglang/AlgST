{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}

module AlgST.Typing
  ( -- * Monad Stack
    TcM,
    runTcM,

    -- * Kinds
    HasKiSt (..),
    HasKiEnv (..),
    KindEnv,
    KiSt (..),
    KiTypingEnv (..),
    kisynth,
    kicheck,

    -- * Types
    TypeM,
    runTypeM,
    TypeEnv,
    TySt (..),
    TyTypingEnv (..),
    Var (..),
    Usage (..),
    tysynth,
    tycheck,
    normalize,

    -- * Programs
    RunTyM,
    RunKiM,
    checkProgram,
    checkWithProgram,
    checkSignature,

    -- * Phase
    Tc,
    TcExp,
    TcExpX (..),
    TcType,
    TcBind,
    TcCaseMap,
    TcProgram,
  )
where

import AlgST.Builtins.Names
import AlgST.Parse.Phase
import AlgST.Rename
import AlgST.Syntax.Decl
import AlgST.Syntax.Expression qualified as E
import AlgST.Syntax.Kind ((<=?))
import AlgST.Syntax.Kind qualified as K
import AlgST.Syntax.Name
import AlgST.Syntax.Program
import AlgST.Syntax.Traversal
import AlgST.Syntax.Type qualified as T
import AlgST.Typing.Equality qualified as Eq
import AlgST.Typing.Error qualified as Error
import AlgST.Typing.Monad
import AlgST.Typing.NormalForm
import AlgST.Typing.Phase
import AlgST.Util
import AlgST.Util.ErrorMessage
import Control.Applicative
import Control.Category ((>>>))
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State.Strict
import Control.Monad.Trans.Maybe
import Control.Monad.Validate
import Data.Bifunctor
import Data.DList.DNonEmpty qualified as DNE
import Data.Either
import Data.Foldable
import Data.Functor.Identity
import Data.List.NonEmpty (NonEmpty (..), nonEmpty, (<|))
import Data.List.NonEmpty qualified as NE
import Data.Map.Merge.Strict qualified as Merge
import Data.Map.Strict qualified as Map
import Data.Maybe
import Data.Monoid (Endo (..))
import Data.Sequence qualified as Seq
import Data.Set qualified as Set
import Data.These
import Data.Tuple qualified as Tuple
import Data.Void
import Lens.Family2
import Lens.Family2.State.Strict
import Syntax.Base hiding (Variable)
import Prelude hiding (lookup, truncate)

-- | Translates the typechecker specific error set representation into a simple
-- list.
runErrors :: Errors -> NonEmpty Diagnostic
runErrors = DNE.toNonEmpty . mergeTheseWith id recursiveErrs (<>)
  where
    recursiveErrs (RecursiveSets oneKeys oneRec recs) =
      DNE.fromNonEmpty $
        Error.cyclicAliases oneRec
          :| fmap Error.cyclicAliases (Map.elems (Map.delete oneKeys recs))

runTypeM :: TyTypingEnv -> TySt -> TypeM a -> RnM (TySt, Either Errors a)
runTypeM = runTcM

runTcM :: env -> s -> TcM env s a -> RnM (s, Either Errors a)
runTcM typesEnv s m =
  Tuple.swap <$> runReaderT (runStateT (runValidateT m) s) typesEnv

type RunTyM = forall env st a. (HasKiEnv env, HasKiSt st) => TypeM a -> TcM env st a

type RunKiM = forall a. TcM KiTypingEnv KiSt a -> RnM (Either (NonEmpty Diagnostic) a)

checkWithProgram ::
  Program Rn ->
  (RunTyM -> RunKiM -> TcProgram -> RnM (Either (NonEmpty Diagnostic) r)) ->
  RnM (Either (NonEmpty Diagnostic) r)
checkWithProgram prog k = runExceptT $ do
  let runWrapExcept st m = ExceptT . fmap (first runErrors . sequence) $ runTcM kiEnv st m
  (st, (tcTypes, tcValues, tcImports)) <- runWrapExcept st0 checkGlobals
  let importedValues = Map.map (ValueGlobal Nothing . signatureType) tcImports
  let tyEnv =
        TyTypingEnv
          { tcCheckedTypes = tcTypes,
            tcCheckedValues = tcValues <> importedValues,
            tcKiTypingEnv = kiEnv
          }
  let -- Not eta-reduced because of the monomorphism restriction.
      embed m = embedTypeM tyEnv m
  let mkProg values =
        Program
          { programTypes = tcTypes,
            programValues = values,
            programImports = tcImports
          }
  (st', prog) <- runWrapExcept st $ mkProg <$> checkValueBodies embed tcValues
  ExceptT $ k embed (fmap (first runErrors . snd) . runTcM kiEnv st') prog
  where
    kiEnv =
      KiTypingEnv
        { tcKindEnv = mempty,
          tcExpansionStack = mempty,
          tcContext = prog,
          -- TODO: Use the actual module here!
          tcModule = Module ""
        }
    st0 =
      KiSt
        { tcAliases =
            let getAlias _ decl = Identity do
                  AliasDecl origin alias <- pure decl
                  pure $ UncheckedAlias (pos origin) alias
             in runIdentity $ Map.traverseMaybeWithKey getAlias $ programTypes prog
        }
    checkGlobals = do
      checkAliases (Map.keys (programTypes prog))
      tcTypes <- checkTypeDecls (programTypes prog)
      checkedDefs <- checkValueSignatures (programValues prog)
      tcImports <- traverse checkSignature (programImports prog)
      pure (tcTypes, checkedConstructors tcTypes <> checkedDefs, tcImports)

checkProgram :: Program Rn -> RnM (Either (NonEmpty Diagnostic) TcProgram)
checkProgram p = checkWithProgram p \_ _ -> pure . Right

addError :: MonadValidate Errors m => Diagnostic -> m ()
addError !e = dispute $ This $ DNE.singleton e

-- | Records multiple errors. If the error list is acutally empty, no errors
-- will be recorded and the computation won't fail.
addErrors :: MonadValidate Errors m => [Diagnostic] -> m ()
addErrors = maybe (pure ()) (dispute . This . DNE.fromNonEmpty) . nonEmpty

addFatalError :: MonadValidate Errors m => Diagnostic -> m a
addFatalError !e = refute $ This $ DNE.singleton e

maybeError :: MonadValidate Errors m => Diagnostic -> Maybe a -> m a
maybeError e = maybe (addFatalError e) pure

useVar :: MonadValidate Errors m => Pos -> ProgVar -> Var -> m Var
useVar loc name v = case varUsage v of
  UnUsage ->
    pure v
  LinUnunsed ->
    pure v {varUsage = LinUsed loc}
  LinUsed ppos -> do
    addError (Error.linVarUsedTwice ppos loc name v)
    pure v

checkTypeDecls :: (HasKiEnv env, HasKiSt st) => TypesMap Rn -> TcM env st (TypesMap Tc)
checkTypeDecls = Map.traverseMaybeWithKey checkTypeDecl

-- | Checks the given type declaration. Nothing is done for 'AliasDecl's. The
-- returned map contains the checked constructors.
checkTypeDecl ::
  (HasKiEnv env, HasKiSt st) => TypeVar -> TypeDecl Rn -> TcM env st (Maybe (TypeDecl Tc))
checkTypeDecl name = \case
  AliasDecl _ _ ->
    pure Nothing
  DataDecl origin decl -> do
    -- Builtin declarations are allowed to be declared with a kind of ML or MU
    -- as well.
    let alwaysAllowed =
          K.TL :| [K.TU]
    let allowed
          -- A builtin declaration may declare types as ML/MU. Usually only
          -- TL/TU is allowed.
          | isBuiltin origin = K.ML <| K.MU <| alwaysAllowed
          | otherwise = alwaysAllowed
    kind <- expectNominalKind (pos origin) "data" name (nominalKind decl) allowed
    tcConstructors <- local (bindParams (nominalParams decl)) do
      traverseConstructors (checkDataCon kind) (nominalConstructors decl)
    pure $ Just $ DataDecl origin decl {nominalConstructors = tcConstructors}
  ProtoDecl origin decl -> do
    _ <- expectNominalKind (pos origin) "protocol" name (nominalKind decl) (K.P :| [])
    tcConstructors <- local (bindParams (nominalParams decl)) do
      traverseConstructors (const checkProtoCon) (nominalConstructors decl)
    pure $ Just $ ProtoDecl origin decl {nominalConstructors = tcConstructors}
  where
    checkDataCon k _name field =
      kicheck field k
    checkProtoCon ty = do
      (ty', k) <- kisynth ty
      ty' <$ expectSubkind ty k [K.TL defaultPos, K.P defaultPos]

-- | Makes sure all aliases are expanded. This step is to make sure all invalid
-- type aliases are diagnosed even when they are not used.
checkAliases :: (Foldable f, HasKiEnv env, HasKiSt st) => f TypeVar -> TcM env st ()
checkAliases =
  -- Type aliases are expanded by looking them up.
  traverse_ $ runMaybeT . lookupTypeAlias

-- | Typechecks the signatures of the contained 'ValueDecl's. The resulting map
-- does not contain any 'ValueCon's. Checked constructors are returned by
-- 'checkTypeDecl'/'checkTypeDecls'.
checkValueSignatures :: (HasKiEnv env, HasKiSt st) => ValuesMap Rn -> TcM env st TcValuesMap
checkValueSignatures = Map.traverseMaybeWithKey $ const \case
  Left _ -> do
    -- The reason for dropping the construcutors here is twofold:
    -- 1. It duplicates some work from 'checkTypeDecl', which by itself is not that bad.
    -- 2. It would therefore duplicate some error messages.
    pure Nothing
  Right decl ->
    Just . ValueGlobal (Just decl) . signatureType
      <$> checkSignature (valueSignatureDecl decl)

checkedConstructors :: TypesMap Tc -> TcValuesMap
checkedConstructors = Map.foldMapWithKey \name ->
  Map.map ValueCon . declConstructors originAt originAt name

checkSignature :: (HasKiEnv env, HasKiSt st) => SignatureDecl Rn -> TcM env st (SignatureDecl Tc)
checkSignature (SignatureDecl x ty) =
  SignatureDecl x <$> kicheck ty (K.TU (pos x))

checkValueBodies ::
  (forall a. TypeM a -> TcM env st a) -> TcValuesMap -> TcM env st (ValuesMap Tc)
checkValueBodies embed = Map.traverseMaybeWithKey \_name -> \case
  ValueCon condecl -> do
    -- Constructors have no body to check.
    pure $ Just $ Left condecl
  ValueGlobal (Just vd) ty -> do
    -- Align the binds with the values type and check the body.
    body <- embed $ checkAlignedBinds ty (valueParams vd) (valueBody vd)
    pure $ Just $ Right vd {valueType = ty, valueBody = body}
  ValueGlobal Nothing _ -> do
    -- Non-global values are not possible on this level.
    pure Nothing

embedTypeM :: HasKiSt s => TyTypingEnv -> TypeM a -> TcM env s a
embedTypeM env m = do
  kist <- use kiStL
  let tyst =
        TySt
          { tcKindSt = kist,
            tcTypeEnv = mempty
          }
  (st, res) <- liftRn $ runTypeM env tyst m
  kiStL .= view kiStL st
  case res of
    Left errs -> refute errs
    Right a -> pure a

checkAlignedBinds :: TcType -> [Located AName] -> RnExp -> TypeM TcExp
checkAlignedBinds fullTy allVs e = go fullTy fullTy allVs
  where
    go :: TcType -> TcType -> [Located AName] -> TypeM TcExp
    go _ t [] = tycheck e t
    go _ (T.Arrow k mul t u) (p :@ Right pv : vs) = do
      withProgVarBind (unrestrictedLoc k mul) p pv t do
        E.Abs defaultPos . E.Bind defaultPos mul pv t <$> go u u vs
    go _ t0@(T.Forall _ (K.Bind _ sigVar k t)) vs0@(p :@ v : vs) = do
      let subBind tv = substituteType @_ @Tc (Map.singleton sigVar (T.Var k tv))
      let wrapAbs tv = E.TypeAbs @Tc defaultPos . K.Bind p tv k
      case v of
        Left tv -> do
          local (bindTyVar tv k) do
            wrapAbs tv <$> go t (subBind tv t) vs
        Right _ -> do
          -- Skip the type abstraction by binding a wildcard pattern. Keep the
          -- expected type for the error message.
          wildTV <- liftRn $ bindOne (mkPxy () @Parse @Rn) Wildcard pure
          wrapAbs wildTV <$> go t0 (subBind wildTV t) vs0
    go t _ (v : _) = do
      -- The bind ›v‹ does not align with the expected type. While trying to
      -- align it the expected type got more and more destructured. The first
      -- argument to 'go' is the un-destructured expected type.
      addFatalError $ uncurryL Error.mismatchedBind v t

expectNominalKind ::
  MonadValidate Errors m => Pos -> String -> TypeVar -> K.Kind -> NonEmpty (Pos -> K.Kind) -> m K.Kind
expectNominalKind loc nomKind name actual allowed' = do
  let allowed = ($ defaultPos) <$> allowed'
  if actual `elem` allowed
    then pure actual
    else NE.last allowed <$ addError (Error.invalidNominalKind loc nomKind name actual allowed)

-- | Checks if a type alias with the given name exists and if so returns the
-- fully expanded alias.
--
-- The alias parameters have to be checked against 'aliasParams' and substitued
-- into 'aliasType' by the caller.
lookupTypeAlias ::
  (HasKiEnv env, HasKiSt s) => TypeVar -> MaybeT (TcM env s) (TypeAlias Tc, K.Kind)
lookupTypeAlias name = do
  alias <- MaybeT $ use $ kiStL . tcAliasesL . to (Map.lookup name)
  lift case alias of
    CheckedAlias ta k ->
      pure (ta, k)
    RecursiveAlias recs ->
      refute (That recs)
    UncheckedAlias pos ta -> do
      depth <- asks $ view kiEnvL >>> tcExpansionStack >>> length
      setAlias (ExpandingAlias depth)
      (expanded, k) <- local (noteExpansion pos ta) do
        case aliasKind ta of
          Nothing -> kisynth (aliasType ta)
          Just k -> (,k) <$> kicheck (aliasType ta) k
      let checked = ta {aliasType = expanded}
      setAlias (CheckedAlias checked k)
      pure (checked, k)
    ExpandingAlias depth -> do
      recs@(RecursiveSets names _ _) <-
        asks $
          view kiEnvL
            >>> tcExpansionStack
            >>> toList
            >>> drop depth
            >>> buildRecsError
      let diagnosed = Map.fromSet (const (RecursiveAlias recs)) names
      kiStL . tcAliasesL %= Map.union diagnosed
      refute $ That recs
  where
    setAlias a =
      kiStL . tcAliasesL %= Map.insert name a
    noteExpansion pos alias env =
      env
        & kiEnvL . tcExpansionStackL %~ (Seq.|> (pos, name, alias))
        & bindParams (aliasParams alias)
    buildRecsError recSet =
      let names = Set.fromList [name | (_, name, _) <- recSet]
       in RecursiveSets names recSet (Map.singleton names recSet)

-- | @typeAppBase t us@ destructures @t@ multiple levels to the type
-- application head. @us@ is a non-empty list of already established
-- parameters.
--
-- The "head" must be a type constructor because the type system does not
-- support higher-kinded types.
--
-- The result is a tuple consisting of the head location, the head, and
-- parameters (including @us@).
typeAppBase :: forall env st. RnType -> NonEmpty RnType -> TcM env st (Pos, TypeVar, [RnType])
typeAppBase = flip go
  where
    go :: NonEmpty RnType -> RnType -> TcM env st (Pos, TypeVar, [RnType])
    go us = \case
      T.Con p c -> pure (p, c, toList us)
      T.App _ t u -> go (u <| us) t
      t -> addFatalError $ err us t
    err :: NonEmpty RnType -> RnType -> Diagnostic
    err us t = Error.typeConstructorNParams (pos t) (t <| us) (length us) 0

kisynthTypeCon ::
  (HasKiEnv env, HasKiSt st) => Pos -> TypeVar -> [RnType] -> TcM env st (TcType, K.Kind)
kisynthTypeCon loc name args =
  runMaybeT (alias <|> decl) >>= maybeError (Error.undeclaredCon loc name)
  where
    alias = do
      (alias, k) <- lookupTypeAlias name
      subs <- lift $ zipTypeParams loc name (aliasParams alias) args
      pure (substituteType (Map.fromList subs) (aliasType alias), k)

    decl = do
      decl <-
        MaybeT . asks $
          view kiEnvL
            >>> tcContext
            >>> programTypes
            >>> Map.lookup name
      subs <- lift $ zipTypeParams loc name (declParams decl) args
      let kind = case decl of
            AliasDecl {} -> error "unexpected AliasDecl"
            DataDecl _ tn -> nominalKind tn
            ProtoDecl _ tn -> nominalKind tn
      let refTy =
            TypeRef
              { typeRefPos = loc,
                typeRefKind = kind,
                typeRefName = name,
                typeRefArgs = snd <$> subs
              }
      pure (T.Type refTy, kind)

-- | Kind-checks the types against the parameter list. In case they differ in
-- length an error is emitted.
zipTypeParams ::
  (HasKiEnv env, HasKiSt st) =>
  Pos ->
  TypeVar ->
  Params ->
  [RnType] ->
  TcM env st [(TypeVar, TcType)]
zipTypeParams loc name ps0 ts0 = go 0 ps0 ts0
  where
    go !_ [] [] = pure []
    go !n ((_ :@ v, k) : ps) (a : as) =
      liftA2
        (:)
        ((v,) <$> kicheck a k)
        (go (n + 1) ps as)
    go !n ps as =
      addFatalError $
        Error.typeConstructorNParams
          loc
          (T.Con loc name :| ts0)
          (n + length as)
          (n + length ps)

-- | Builds a substitutions map based on 'declParams' and 'typeRefArgs'.
typeRefSubstitutions :: TypeDecl Tc -> TypeRef -> Substitutions Tc
typeRefSubstitutions decl ref =
  typeSubstitions . Map.fromList $
    zip (unL . fst <$> declParams decl) (typeRefArgs ref)

-- | Applies a substitution to a 'TypeDecl'.
--
-- /Note:/ The substitution only applies to the constructors and their items. Most notably the
substituteTypeConstructors :: Substitutions Tc -> TypeDecl Tc -> Constructors TcType
substituteTypeConstructors subs = nomDecl >>> substituteConstructors
  where
    nomDecl = \case
      AliasDecl x _ -> absurd x
      DataDecl _ d -> d
      ProtoDecl _ d -> d
    substituteConstructors nom =
      mapConstructors (const $ applySubstitutions subs) (nominalConstructors nom)

kisynth :: (HasKiEnv env, HasKiSt st) => RnType -> TcM env st (TcType, K.Kind)
kisynth =
  etaTcM . \case
    T.Unit p -> do
      pure (T.Unit p, K.MU p)
    T.Var p v -> do
      mk <- asks $ view kiEnvL >>> tcKindEnv >>> Map.lookup v
      k <- flip K.relocate p <$> maybeError (Error.unboundVar p v) mk
      pure (T.Var k v, k)
    T.Con p v -> do
      kisynthTypeCon p v []
    T.App _ t u -> do
      (p, c, args) <- typeAppBase t (pure u)
      kisynthTypeCon p c args
    T.Arrow p m t1 t2 -> do
      (t1', t2') <-
        -- Applicatively to get error messages from both branches.
        (,)
          <$> kicheck t1 (K.TL p)
          <*> kicheck t2 (K.TL p)
      let k = K.Kind p K.Top m
      pure (T.Arrow p m t1' t2', k)
    T.Forall _ (K.Bind p v k t) -> do
      local (bindTyVar v k) do
        (t', tyk) <- kisynth t
        case K.multiplicity tyk of
          Just m -> do
            let forallK = K.Kind p K.Top m
                forallT = T.Forall p (K.Bind p v k t')
            pure (forallT, forallK)
          Nothing -> do
            addFatalError (Error.unexpectedKind t tyk [])
    T.Pair p t1 t2 -> do
      ((t1', k1), (t2', k2)) <- do
        -- Applicatively to get error messages from both branches.
        (,)
          <$> kisynth t1
          <*> kisynth t2

      -- Make sure none of the components have kind P.
      expectSubkind t1 k1 [K.TL defaultPos]
      expectSubkind t2 k2 [K.TL defaultPos]

      -- Calculate the pair's kind:   k1 |_| k2 |_| TU
      --
      -- The TU is there so that a pair does not get a M* kind. See section
      -- "Kind polymorphism for pairs".
      let k = K.leastUpperBound (K.leastUpperBound k1 k2) (K.TU defaultPos)
      pure (T.Pair p t1' t2', k)
    T.End p -> do
      pure (T.End p, K.SU p)
    T.Session p pol t1 t2 -> do
      t1' <- kicheck t1 $ K.P p
      t2' <- kicheck t2 $ K.SL p
      pure (T.Session p pol t1' t2', K.SL p)
    T.Dualof p t -> do
      (t', k) <- kisynth t
      checkSubkind t k (K.SL p)
      pure (T.Dualof p t', k)
    T.Negate p t -> do
      t' <- kicheck t (K.P p)
      pure (T.Negate p t', K.P p)
    T.Type x ->
      absurd x

kicheck :: (HasKiEnv env, HasKiSt st) => RnType -> K.Kind -> TcM env st TcType
kicheck t k = do
  (t', k') <- kisynth t
  expectSubkind t k' [k]
  pure t'

checkSubkind :: MonadValidate Errors m => RnType -> K.Kind -> K.Kind -> m ()
checkSubkind t k1 k2 = errorIf (not (k1 <=? k2)) (Error.unexpectedKind t k1 [k2])

tysynth :: RnExp -> TypeM (TcExp, TcType)
tysynth =
  etaTcM . \case
    E.Lit p l -> do
      let t = litType p l
      pure (E.Lit p l, t)

    --
    E.Pair p e1 e2 -> do
      ((e1', t1), (e2', t2)) <-
        (,)
          <$> tysynth e1
          <*> tysynth e2

      let t = T.Pair p t1 t2
      pure (E.Pair p e1' e2', t)

    --
    E.Var p v -> do
      synthVariable p v >>= maybeError (Error.unboundVar p v)

    --
    E.Con p v -> do
      synthVariable p v >>= maybeError (Error.undeclaredCon p v)

    --
    E.Abs p bnd -> do
      (bnd', ty) <- tysynthBind p bnd
      pure (E.Abs p bnd', ty)

    --
    E.TypeAbs p bnd -> do
      (bnd', ty) <- tysynthTyBind tysynth p bnd
      pure (E.TypeAbs p bnd', ty)

    --
    E.App p (E.Exp (BuiltinFork _)) e -> do
      -- TODO: Desugar to `fork_`. The hard part is getting the reference to
      -- `send` correct since it is not more than a "imported" signature which
      -- might be shadowed.
      (e', ty) <- tysynth e
      let k = typeKind ty
      when (not (k <=? K.ML defaultPos)) do
        addError $ Error.unexpectedForkKind "fork" e ty k $ K.ML defaultPos
      let resultTy = buildSessionType p T.In [ty] $ T.End p
      pure (E.Fork p e', resultTy)

    --
    E.App p (E.Exp (BuiltinFork_ _)) e -> do
      (e', ty) <- tysynth e
      let k = typeKind ty
      when (not (k <=? K.TU defaultPos)) do
        addError $ Error.unexpectedForkKind "fork_" e ty k $ K.TU defaultPos
      pure (E.Fork_ p e', T.Unit p)

    --
    E.App p e1 e2 -> do
      (e1', t1) <- tysynth e1
      (t, u) <-
        maybeError
          (Error.noArrowType e1 t1)
          (appArrow t1)
      e2' <- tycheck e2 t
      pure (E.App p e1' e2', u)

    --
    E.TypeApp _ (E.Exp (BuiltinNew p)) t -> do
      t' <- kicheck t $ K.SL p
      let newT = T.Pair p t' (T.Dualof p t')
      pure (E.New p t', newT)
    E.TypeApp p e t -> do
      (e', eTy) <- tysynth e
      K.Bind _ v k u <-
        maybeError
          (Error.noForallType e eTy)
          (appTArrow eTy)
      t' <- kicheck t k
      let u' = substituteType (Map.singleton v t') u
      pure (E.TypeApp p e' t', u')

    --
    E.Rec p v ty r -> do
      -- Check for TU is deliberate here. It is unclear if a linear value would
      -- be well behaved.
      ty' <- kicheck ty (K.TU p)
      withProgVarBind Nothing p v ty' do
        (r', rTy) <- tysynthRecLam r
        requireEqual (E.RecAbs r) ty' rTy
        pure (E.Rec p v ty' r', ty')

    -- 'let' __without__ a type signature.
    E.UnLet p v Nothing e body -> do
      (e', eTy) <- tysynth e
      withProgVarBind Nothing p v eTy do
        (body', bodyTy) <- tysynth body
        let branch =
              E.CaseBranch
                { branchPos = p,
                  branchBinds = Identity (p :@ v),
                  branchExp = body'
                }
        let caseMap =
              E.CaseMap
                { E.casesWildcard = Just branch,
                  E.casesPatterns = Map.empty
                }
        pure (E.Exp $ ValueCase p e' caseMap, bodyTy)

    -- 'let' __with__ a type signature.
    E.UnLet p v (Just ty) e body -> do
      ty' <- kicheck ty (K.TL p)
      e' <- tycheck e ty'
      withProgVarBind Nothing p v ty' do
        (body', bodyTy) <- tysynth body
        let branch =
              E.CaseBranch
                { branchPos = p,
                  branchBinds = Identity (p :@ v),
                  branchExp = body'
                }
        let caseMap =
              E.CaseMap
                { E.casesWildcard = Just branch,
                  E.casesPatterns = Map.empty
                }
        pure (E.Exp $ ValueCase p e' caseMap, bodyTy)

    --
    E.PatLet p c vs e body -> do
      (e', eTy) <- tysynth e
      pat <- extractMatchableType "Pattern let expression" (pos e) eTy
      let branch =
            E.CaseBranch
              { branchPos = p,
                branchExp = body,
                branchBinds = vs
              }
      let cases =
            E.CaseMap
              { casesPatterns = Map.singleton c branch,
                casesWildcard = Nothing
              }
      checkPatternExpression p e' cases pat

    --
    E.Cond p e eThen eElse -> do
      (e', eTy) <- tysynth e

      (mty, (eThen', eElse')) <- runBranchT p do
        (,)
          <$> liftBranchT (Error.CondThen (pos eThen)) (checkOrSynth eThen)
          <*> liftBranchT (Error.CondElse (pos eElse)) (checkOrSynth eElse)
      let ty = error "impossible: branches have no type" `fromMaybe` mty

      hasBool <- asks (isBoolType eTy)
      when (not hasBool) do
        addError (Error.expectedBool (pos e) eTy)

      let branches =
            Map.fromList
              [ (ConTrue, E.CaseBranch (pos eThen) [] eThen'),
                (ConFalse, E.CaseBranch (pos eElse) [] eElse')
              ]
      let eCase =
            E.Exp . ValueCase p e' $
              E.CaseMap
                { casesPatterns = branches,
                  casesWildcard = Nothing
                }
      pure (eCase, ty)

    --
    E.Case p e cases -> do
      (e', eTy) <- tysynth e
      pat <- extractMatchableType "Case expression scrutinee" (pos e) eTy
      checkPatternExpression p e' cases pat

    --
    E.Select p lcon@(_ :@ PairCon) -> do
      v1 <- freshLocal "a"
      v2 <- freshLocal "b"
      let tyX = T.Var @Tc kiX
          kiX = K.TL defaultPos
      let params = [(p :@ v1, kiX), (p :@ v2, kiX)]
          pairTy = T.Pair defaultPos (tyX v1) (tyX v2)
      ty <- buildSelectType p params pairTy [tyX v1, tyX v2]
      pure (E.Select p lcon, ty)

    --
    E.Select p lcon@(_ :@ con) -> do
      let findConDecl = runMaybeT do
            ValueCon conDecl <- MaybeT $ asks $ tcCheckedValues >>> Map.lookup con
            parentDecl <- MaybeT $ asks $ tcCheckedTypes >>> Map.lookup (conParent conDecl)
            pure (conDecl, parentDecl)
      (conDecl, parentDecl) <- maybeError (uncurryL Error.undeclaredCon lcon) =<< findConDecl
      (params, ref) <- instantiateDeclRef defaultPos (conParent conDecl) parentDecl
      let sub = applySubstitutions (typeRefSubstitutions parentDecl ref)
      ty <- buildSelectType p params (T.Type ref) (sub <$> conItems conDecl)
      pure (E.Select p lcon, ty)

    --
    e@(E.Exp (BuiltinNew _)) -> do
      addFatalError $ Error.builtinMissingApp e "a type application"
    e@(E.Exp (BuiltinFork _)) -> do
      addFatalError $ Error.builtinMissingApp e "an expression"
    e@(E.Exp (BuiltinFork_ _)) -> do
      addFatalError $ Error.builtinMissingApp e "an expression"

    --
    E.New x _ -> absurd x
    E.Fork x _ -> absurd x
    E.Fork_ x _ -> absurd x

buildSelectType :: HasKiEnv env => Pos -> Params -> TcType -> [TcType] -> TcM env st TcType
buildSelectType p params t us = do
  varS <- freshLocal "s"
  let tyS = T.Var @Tc kiS varS
      kiS = K.SL defaultPos
  let foralls = buildForallType params . buildForallType [(p :@ varS, kiS)]
  let arrLhs = buildSessionType defaultPos T.Out [t]
      arrRhs = buildSessionType defaultPos T.Out us
  let ty = foralls $ T.Arrow p Un (arrLhs tyS) (arrRhs tyS)
  pure ty

data PatternType
  = PatternRef TypeRef
  | PatternPair (T.XPair Tc) TcType TcType

-- | Reconstructs the original 'TcType'.
originalPatternType :: PatternType -> TcType
originalPatternType = \case
  PatternRef r -> T.Type r
  PatternPair x t1 t2 -> T.Pair x t1 t2

patternBranches :: PatternType -> TypeM (NameMap Values [TcType])
patternBranches = \case
  PatternRef ref -> do
    let subst d = substituteTypeConstructors (typeRefSubstitutions d ref) d
    mdecl <- asks $ tcCheckedTypes >>> Map.lookup (typeRefName ref)
    fmap (fmap snd . subst) $
      maybeError (Error.undeclaredCon (typeRefPos ref) (typeRefName ref)) mdecl
  PatternPair _ t1 t2 ->
    pure $ Map.singleton PairCon [t1, t2]

data MatchableType
  = MatchValue PatternType
  | MatchSession PatternType TcType

-- | Checks if a pattern match is possible on a value of the given type. A
-- 'Left' result indicates an ordinary pattern match. A 'Right' result
-- indicates a receiving match on a session type.
--
-- In case the type is not suitable an error is emitted.
extractMatchableType :: String -> Pos -> TcType -> TcM env s MatchableType
extractMatchableType s p t = etaTcM do
  tNF <- normalize t
  let patTy = \case
        T.Type ref -> Just $ PatternRef ref
        T.Pair x t1 t2 -> Just $ PatternPair x t1 t2
        _ -> Nothing
  case tNF of
    T.Session _ T.In (patTy -> Just p) s ->
      pure $ MatchSession p s
    (patTy -> Just p) ->
      pure $ MatchValue p
    _ ->
      addFatalError $ Error.invalidPatternExpr s p t tNF

-- | Checks that the given type references the builtin @Bool@ type.
--
-- When the refences type is a data declaration with 'OriginBuiltin' we are
-- satisfied.
isBoolType :: TcType -> TyTypingEnv -> Bool
isBoolType ty env
  | -- Is it a reference to some parameter-less type named "Bool"?
    T.Type
      TypeRef
        { typeRefName = name@(Builtin "Bool"),
          typeRefArgs = []
        } <-
      ty,
    -- Does it reference a builtin data declaration?
    Just (DataDecl OriginBuiltin _) <-
      Map.lookup name (tcCheckedTypes env) =
    True
  | otherwise =
    False

-- | Looks up the type for the given 'ProgVar'. This function works correctly
-- for local variables, globals and constructors.
synthVariable :: Pos -> ProgVar -> TypeM (Maybe (TcExp, TcType))
synthVariable p name = runMaybeT (useLocal <|> useGlobal)
  where
    useLocal = do
      info <- MaybeT $ gets $ tcTypeEnv >>> Map.lookup name
      used <- useVar p name info
      tcTypeEnvL %= Map.insert name used
      pure (E.Var p name, varType info)

    useGlobal = do
      global <- MaybeT $ asks $ tcCheckedValues >>> Map.lookup name
      case global of
        ValueGlobal _ ty ->
          pure (E.Var p name, ty)
        ValueCon (DataCon _ parent _ mul items) -> do
          decl <- MaybeT $ asks $ tcCheckedTypes >>> Map.lookup parent
          ty <- lift $ buildDataConType p parent decl mul items
          pure (E.Con p name, ty)
        ValueCon (ProtocolCon _ parent _ _) ->
          addFatalError $ Error.protocolConAsValue p name parent

instantiateDeclRef ::
  Pos -> TypeVar -> TypeDecl Tc -> TcM env s (Params, TypeRef)
instantiateDeclRef p name decl = do
  params <- liftRn $ freshParamsNC (declParams decl)
  pure
    ( params,
      TypeRef
        { typeRefName = name,
          typeRefKind = tcDeclKind decl,
          typeRefPos = p,
          typeRefArgs = (\(_ :@ tv, k) -> T.Var k tv) <$> params
        }
    )

-- | Tries to destructure a type into into domain and codomain of an arrow.
-- This includes applying the forall isomorphism to push quantified type
-- variables further down if allowed.
appArrow :: TcType -> Maybe (TcType, TcType)
appArrow = go id Set.empty
  where
    go prependPushed pushed = \case
      T.Arrow _ _ t u
        | not (liftNameSet pushed `anyFree` t) ->
          Just (t, prependPushed u)
      T.Forall x (K.Bind x' v k t) ->
        go
          (prependPushed . T.Forall x . K.Bind x' v k)
          (Set.insert v pushed)
          t
      _ ->
        Nothing

appTArrow :: TcType -> Maybe (K.Bind TcType)
appTArrow = go id
  where
    go prependArrows = \case
      T.Forall _ (K.Bind x' v k t) ->
        Just (K.Bind x' v k $ prependArrows t)
      T.Arrow x m t u ->
        go (prependArrows . T.Arrow x m t) u
      _ ->
        Nothing

checkPatternExpression ::
  Pos -> TcExp -> RnCaseMap -> MatchableType -> TypeM (TcExp, TcType)
checkPatternExpression loc scrut cases pat = do
  case pat of
    MatchSession pat s -> do
      (cases', ty) <- checkSessionCase loc cases pat s
      pure (E.Exp $ RecvCase loc scrut cases', ty)
    MatchValue pat -> do
      (cases', ty) <- checkStandardCase loc cases pat
      pure (E.Exp $ ValueCase loc scrut cases', ty)

checkStandardCase ::
  Pos -> RnCaseMap -> PatternType -> TypeM (TcCaseMap [] Maybe, TcType)
checkStandardCase loc cases patTy =
  checkCaseExpr loc True cases patTy \con fields b -> etaTcM do
    -- Check that the number of binds matches the number of fields.
    let nGiven = length (E.branchBinds b)
        nExpected = length fields
    errorIf (nGiven /= nExpected) $
      Error.branchPatternBindingCount (pos b) con nExpected nGiven
    -- Return the typed binds.
    pure (zip (E.branchBinds b) fields)

-- | Combines a list of @('TypeVar', 'K.Kind')@ pairs into a nested 'T.Forall'
-- type.
buildForallType :: Params -> TcType -> TcType
buildForallType = foldMap (Endo . mkForall) >>> appEndo
  where
    mkForall :: (Located TypeVar, K.Kind) -> TcType -> TcType
    mkForall (p :@ tv, k) = T.Forall defaultPos . K.Bind p tv k

buildDataConType ::
  Pos -> TypeVar -> TypeDecl Tc -> Multiplicity -> [TcType] -> TcM env s TcType
buildDataConType p name decl mul items = do
  (params, ref) <- instantiateDeclRef p name decl
  let subs = typeRefSubstitutions decl ref
  let conArrow = foldr (T.Arrow defaultPos mul) (T.Type ref) (applySubstitutions subs <$> items)
  pure $ buildForallType params conArrow

buildSessionType :: Pos -> T.Polarity -> [TcType] -> TcType -> TcType
buildSessionType loc pol fields s = foldr (T.Session loc pol) s fields

checkSessionCase ::
  Pos -> RnCaseMap -> PatternType -> TcType -> TypeM (TcCaseMap Identity (Const ()), TcType)
checkSessionCase loc cases patTy s = do
  (cmap, ty) <- checkCaseExpr loc False cases patTy \_con fields b -> etaTcM do
    -- Get the variable to bind and its type.
    let vTy = buildSessionType (pos b) T.In fields s
    v <- maybeError (Error.invalidSessionCaseBranch b) $ case E.branchBinds b of
      [v] -> Just v
      _ -> Nothing
    pure $ Identity (v, vTy)
  -- A potential wildcard is already diagnosed by 'checkCaseExpr'.
  pure (cmap {E.casesWildcard = Const ()}, ty)

checkCaseExpr ::
  forall f.
  Traversable f =>
  Pos ->
  Bool ->
  RnCaseMap ->
  PatternType ->
  (ProgVar -> [TcType] -> E.CaseBranch [] Rn -> TypeM (f (Located ProgVar, TcType))) ->
  TypeM (TcCaseMap f Maybe, TcType)
checkCaseExpr loc allowWild cmap patTy typedBinds = etaTcM do
  allBranches <- patternBranches patTy

  -- Diagnose missing branches / superfluous wildcards.
  let missingBranches = Map.keys $ allBranches `Map.difference` E.casesPatterns cmap
  let hasMissingBranches = not $ null missingBranches
  let hasValidWildcard = allowWild && isJust (E.casesWildcard cmap)
  errorIf (hasMissingBranches && not hasValidWildcard) do
    Error.missingCaseBranches loc missingBranches

  -- Handles a single (written by the user) branch.
  let go :: ProgVar -> E.CaseBranch [] Rn -> BranchT TcType TypeM (E.CaseBranch f Tc)
      go con branch = liftBranchT (Error.PatternBranch (pos branch) con) \mty -> do
        let branchError =
              Error.mismatchedCaseConstructor
                (pos branch)
                (originalPatternType patTy)
                con
        -- Check that the constructor is valid for the matched type.
        fields <- maybeError branchError $ Map.lookup con allBranches
        -- Check that the bindings correspond with the fields, establish their
        -- types.
        binds <- typedBinds con fields branch
        -- Check the branch expression in the context of the typed bindings.
        (e, eTy) <- withProgVarBinds Nothing (toList binds) do
          checkOrSynth (E.branchExp branch) mty
        pure (branch {E.branchExp = e, E.branchBinds = fst <$> binds}, eTy)

  let goWild :: E.CaseBranch Identity Rn -> BranchT TcType TypeM (E.CaseBranch Identity Tc)
      goWild branch = liftBranchT (Error.WildcardBranch $ pos branch) \mty -> do
        errorIf (not hasMissingBranches) $ Error.unnecessaryWildcard (pos branch)
        errorIf (not allowWild) $ Error.wildcardNotAllowed (pos branch) loc
        let binds = (,originalPatternType patTy) <$> E.branchBinds branch
        (e, eTy) <- withProgVarBinds Nothing (toList binds) do
          checkOrSynth (E.branchExp branch) mty
        pure (branch {E.branchExp = e, E.branchBinds = fst <$> binds}, eTy)

  -- Traverse over all written branches.
  (mty, checkedCases) <-
    runBranchT loc $
      E.CaseMap
        <$> Map.traverseWithKey go (E.casesPatterns cmap)
        <*> traverse goWild (E.casesWildcard cmap)

  case mty of
    Nothing -> addFatalError $ Error.emptyCaseExpr loc
    Just ty -> pure (checkedCases, ty)

-- | A monad transformer (usually applied on top of 'TypeM') to typecheck
-- multiple branches of an expression.
--
-- This transformer, together with 'liftBranchT' and 'runBranchT' does the
-- heavy lifting to ensure the branches agree in which variables are consumed.
newtype BranchT r m a
  = BranchT (ValidateT Errors (StateT (Maybe (BranchSt r)) (ReaderT TypeEnv m)) a)
  deriving newtype (Functor, Applicative, Monad)

data BranchSt r = forall b.
  Error.BranchSpec b =>
  BranchSt
  { -- | Variables which have been consumed in at least one of the encountered
    -- branches.
    branchesConsumed :: !(NameMap Values BranchConsumed),
    -- | A previously encountered branch.
    --
    -- Used in error messages in the likes of /… variable is consumed there
    branchesPrevious :: b,
    -- | Additional payload the branches have to agree upon.
    branchesResult :: r
  }

-- | A variable consumed in a branch.
data BranchConsumed = forall b. Error.BranchSpec b => BranchConsumed !b !Var !Pos

checkOrSynth :: RnExp -> Maybe TcType -> TypeM (TcExp, TcType)
checkOrSynth e Nothing = tysynth e
checkOrSynth e (Just t) = (,t) <$> tycheck e t

liftBranchT ::
  (Error.BranchSpec b, MonadState TySt m) => b -> (Maybe r -> m (a, r)) -> BranchT r m a
liftBranchT p m = BranchT do
  initR <- gets (fmap branchesResult)
  initEnv <- ask
  ((a, r), resultEnv) <- lift . lift . lift $ do
    tcTypeEnvL .= initEnv
    (,) <$> m initR <*> use tcTypeEnvL
  let consumed = uncurry (BranchConsumed p) <$> filterAdditionalConsumed initEnv resultEnv
  get >>= \case
    Nothing -> do
      put . Just $
        BranchSt
          { branchesConsumed = consumed,
            branchesPrevious = p,
            branchesResult = r
          }
    Just bst@BranchSt {branchesPrevious = p1} -> do
      checkConsumedOverlap (branchesConsumed bst) p1 consumed p
      put $ Just bst {branchesConsumed = branchesConsumed bst <> consumed, branchesResult = r}
  pure a

runBranchT :: (MonadState TySt m, MonadValidate Errors m) => Pos -> BranchT r m a -> m (Maybe r, a)
runBranchT p (BranchT m) = do
  initEnv <- gets tcTypeEnv
  (a, mResultEnv) <- runReaderT (runStateT (embedValidateT m) Nothing) initEnv
  whenJust mResultEnv \BranchSt {branchesConsumed = consumed} ->
    tcTypeEnvL .= markConsumed p initEnv consumed
  pure (branchesResult <$> mResultEnv, a)

-- | @filterAdditionalConsumed env1 env2@ filters @env2@ down to the variables
-- which were not already consumed in @env1@ but are in @env2@.
--
-- @env1@ and @env2@ should be related in that @env2@ should be derived from
-- @env1@. Any variables whicha appear only in one environment are discarded.
filterAdditionalConsumed :: TypeEnv -> TypeEnv -> NameMap Values (Var, Pos)
filterAdditionalConsumed = Merge.merge Merge.dropMissing Merge.dropMissing (Merge.zipWithMaybeMatched f)
  where
    -- Returns @Just (var, usageLoc)@ iff the variable is unused in the outer
    -- bindings but used in the inner bindings.
    f _ vOuter vInner = do
      -- Uses the 'Maybe' monad, a failing match results in Nothing.
      LinUnunsed <- pure (varUsage vOuter)
      LinUsed loc <- pure (varUsage vInner)
      pure (vInner, loc)

-- | @markConsumed p env vars@ marks all variables in @env@ which appear also
-- as keys in @vars@ as used at @p@. Variables which appear in @vars@ but not
-- in @env@ are ignored.
markConsumed :: Pos -> TypeEnv -> NameMap Values a -> TypeEnv
markConsumed !p = Merge.merge Merge.preserveMissing Merge.dropMissing (Merge.zipWithMatched mark)
  where
    mark _ v _ = v {varUsage = LinUsed p}

-- | Verifies (or emitts the according errors) that the variables consumed in
-- one branch correspond to the variables consumed in another branch.
--
-- Branches @a@ and @b@ should be the branches from which the preceeding maps
-- originated. These are used in the error messages in the form of "… variable
-- is consumed /here/ but not in branch /{a,b}/ …". We cannot take the from the
-- opposing map because it might be empty. The other way round (do not store a
-- branch in 'BranchSpec') does not work either because branches @a@ and @b@
-- might not actually be the branches in which the variables were consumed.
checkConsumedOverlap ::
  (Error.BranchSpec a, Error.BranchSpec b, MonadValidate Errors m) =>
  NameMap Values BranchConsumed ->
  a ->
  NameMap Values BranchConsumed ->
  b ->
  m ()
checkConsumedOverlap m1 other1 m2 other2 = addErrors errors
  where
    errors =
      errs m1 m2 other2 ++ errs m2 m1 other1
    errs x y other =
      [ Error.branchedConsumeDifference name var consume loc other
        | (name, BranchConsumed consume var loc) <- Map.toList (x `Map.difference` y)
      ]

litType :: Pos -> E.Lit -> TcType
litType p = \case
  E.Unit -> T.Unit p
  E.Int _ -> builtinRef TypeInt
  E.Char _ -> builtinRef TypeChar
  E.String _ -> builtinRef TypeString
  where
    builtinRef name =
      T.Type @Tc
        TypeRef
          { typeRefPos = p,
            typeRefName = name,
            typeRefArgs = [],
            typeRefKind = K.MU p
          }

-- | Synthesizes the 'T.Arrow' type of a @"AlgST.Syntax.Expression".'Bind'@
-- (/E-LinAbs/ or /E-UnAbs/).
tysynthBind :: Pos -> E.Bind Rn -> TypeM (E.Bind Tc, TcType)
tysynthBind absLoc (E.Bind p m v ty e) = do
  ty' <- kicheck ty (K.TL defaultPos)
  (e', eTy) <- withProgVarBind (unrestrictedLoc absLoc m) p v ty' (tysynth e)

  -- Construct the resulting type.
  let funTy = T.Arrow absLoc m ty' eTy
  pure (E.Bind p m v ty' e', funTy)

-- | Synthesizes the 'T.Forall' type of a @"AlgST.Syntax.Kind".'K.Bind' a@. The
-- type of @a@ is synthesized with the provided function.
tysynthTyBind :: (a -> TypeM (b, TcType)) -> Pos -> K.Bind a -> TypeM (K.Bind b, TcType)
tysynthTyBind synth p (K.Bind p' v k a) = do
  (a', t) <- local (bindTyVar v k) (synth a)
  let allT = T.Forall p (K.Bind p' v k t)
  pure (K.Bind p' v k a', allT)

tysynthRecLam :: E.RecLam Rn -> TypeM (E.RecLam Tc, TcType)
tysynthRecLam =
  etaTcM . \case
    E.RecTermAbs p b -> do
      (b', t) <- tysynthBind p b
      pure (E.RecTermAbs p b', t)
    E.RecTypeAbs p b -> do
      (b', t) <- tysynthTyBind tysynthRecLam p b
      pure (E.RecTypeAbs p b', t)

unrestrictedLoc :: Position a => a -> Multiplicity -> Maybe Pos
unrestrictedLoc p Un = Just $! pos p
unrestrictedLoc _ Lin = Nothing

freshLocal :: HasKiEnv env => String -> TcM env st (Name s)
freshLocal s = do
  m <- currentModule
  liftRn $ freshNC $ Name m s

-- | Establishes a set of bindings for a nested scope.
--
-- If the nested scope establishes an unrestricted context (such as an
-- unrestricted lambda expression @\(x:T) -> ...@) this function will verify
-- that no linear variables are consumed while checking the nested scope. For
-- this checking to happen the first argument must point to the location which
-- introduces the /unrestricted/ context. 'unrestrictedLoc' can be used as a
-- helper function.
withProgVarBinds ::
  Maybe Pos -> [(Located ProgVar, TcType)] -> TypeM a -> TypeM a
withProgVarBinds !mUnArrLoc vtys action = etaTcM do
  let mkVar (p :@ v, ty) = etaTcM do
        let ki = typeKind ty
        usage <- case K.multiplicity ki of
          Just Lin
            | isWild v -> undefined "add an error, then use UnUsage here"
            | otherwise -> pure LinUnunsed
          Just Un -> pure UnUsage
          Nothing -> UnUsage <$ addError (Error.unexpectedKind ty ki [K.TL defaultPos])
        let var =
              Var
                { varUsage = usage,
                  varType = ty,
                  varLocation = p
                }
        pure (v, var)

  outerVars <- gets tcTypeEnv
  newVars <- Map.fromList <$> traverse mkVar vtys
  tcTypeEnvL <>= newVars
  a <- action
  resultVars <- gets tcTypeEnv

  whenJust mUnArrLoc \arrLoc -> do
    -- When in an unrestricted context check that no linear variables were
    -- consumed.
    addErrors
      [ Error.invalidConsumed arrLoc name var usageLoc
        | (name, (var, usageLoc)) <- Map.toList (filterAdditionalConsumed outerVars resultVars)
      ]

  -- Emit an error for any of the new variables which are still 'UnusedLin'.
  addErrors
    [ Error.missingUse name var
      | (name, var@Var {varUsage = LinUnunsed}) <-
          Map.toList (resultVars `Map.intersection` newVars)
    ]

  -- Continue with the variables as returned from the inner computation because
  -- a linear context may have consumed linear variables from the outer scope.
  tcTypeEnvL .= resultVars `Map.difference` newVars
  pure a

-- | Like 'withProgVarBinds' but for a single binding.
withProgVarBind :: Maybe Pos -> Pos -> ProgVar -> TcType -> TypeM a -> TypeM a
withProgVarBind mp varLoc pv ty = withProgVarBinds mp [(varLoc :@ pv, ty)]

tycheck :: RnExp -> TcType -> TypeM TcExp
tycheck e u = do
  (e', t) <- tysynth e
  requireEqual e t u
  pure e'

requireEqual :: PExp -> TcType -> TcType -> TypeM ()
requireEqual e t1 t2 = do
  nf1 <- normalize t1
  nf2 <- normalize t2
  when (Eq.Alpha nf1 /= Eq.Alpha nf2) do
    addError (Error.typeMismatch e t1 nf1 t2 nf2)

-- | Returns the normalform of the given type or throws an error at the given
-- position.
normalize :: MonadValidate Errors m => TcType -> m TcType
normalize t = case nf t of
  Just t' -> pure t'
  Nothing -> addFatalError (Error.noNormalform t)

bindTyVar :: HasKiEnv env => TypeVar -> K.Kind -> env -> env
bindTyVar v k = kiEnvL . tcKindEnvL %~ Map.insert v k

bindParams :: HasKiEnv env => Params -> env -> env
bindParams ps = kiEnvL . tcKindEnvL <>~ Map.fromList (first unL <$> ps)

errorIf :: MonadValidate Errors m => Bool -> Diagnostic -> m ()
errorIf True e = addError e
errorIf _ _ = pure ()

-- | @expectSubkind t k ks@ verifies that @k@ is a subkind of any of the kinds
-- @ks@. If not it errors and blames @t@ for the wrong kind @k@.
expectSubkind :: MonadValidate Errors m => RnType -> K.Kind -> [K.Kind] -> m ()
expectSubkind t actualKind allowedKinds =
  errorIf
    (not $ any (actualKind <=?) allowedKinds)
    (Error.unexpectedKind t actualKind allowedKinds)
