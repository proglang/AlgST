{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}

module AlgST.Rename
  ( -- * Aliases and Types
    module AlgST.Rename.Phase,

    -- * Renaming
    RnM,
    Globals,
    ModuleMap,
    renameModule,
    renameModuleExtra,
    continueRenameExtra,
    RenameExtra (..),
    renameSyntax,

    -- * Handling imports
    RenameEnv,
    resolveImport,
    resolveImports,
    moduleImportsEnv,
    renameSimple,
  )
where

import AlgST.Builtins.Names qualified as Builtin
import AlgST.Parse.Phase
import AlgST.Rename.Error (MonadErrors, addError, fatalError)
import AlgST.Rename.Error qualified as Error
import AlgST.Rename.Fresh
import AlgST.Rename.Modules
import AlgST.Rename.Phase
import AlgST.Syntax.Decl qualified as D
import AlgST.Syntax.Expression qualified as E
import AlgST.Syntax.Module
import AlgST.Syntax.Name
import AlgST.Syntax.Traversal
import AlgST.Syntax.Type qualified as T
import AlgST.Util
import AlgST.Util.ErrorMessage (DErrors)
import AlgST.Util.Lenses
import AlgST.Util.Lenses qualified as L
import Control.Monad
import Control.Monad.Reader
import Control.Monad.State.Strict
import Control.Monad.Validate
import Data.Bitraversable
import Data.Coerce
import Data.DList qualified as DL
import Data.Foldable
import Data.Functor.Compose
import Data.Generics.Lens.Lite
import Data.HashMap.Strict qualified as HM
import Data.Map qualified as Map
import Data.Maybe
import Data.Monoid
import Data.Semigroup
import Data.Singletons
import GHC.Generics (Generic)
import Lens.Family2
import Lens.Family2.State.Strict ((%=))
import Lens.Family2.Stock
import Syntax.Base

-- | A partial resolve keeps track of a set of identifiers imported under the
-- same name.
--
-- Each identifier is annotated with where it was imported from. This gives the
-- user a bit of leeway when multiple unqualified/equal qualfied imports export
-- the same identifier. An error message is delayed to the usage site.
--
-- The usage of a map strucuture here instead of a simple list is deliberate:
-- This allows the same identifier (same origin) to be imported multiple times
-- and be used without problems. Consider:
--
-- > import M1 (*)
-- > import M1 (someName)
--
-- Although this use case is relatively contrived it would be quite stranger to
-- emit an error at the usage site of @someName@ along the lines of “Did you
-- mean @M1.someName@ or @M1.someName@?”.
--
-- This type has intentionally no 'Monoid' instance since it should always
-- contain at least one element. Its 'Semigroup' instance merges the maps and
-- chooses the first 'Error.AmbigousOrigin' in case of a duplicate import.
data PartialResolve scope
  = PartialResolve !(Map.Map (NameR scope) Error.AmbiguousOrigin)
  | UniqueLocal !(NameR scope)

instance Semigroup (PartialResolve scope) where
  PartialResolve x <> PartialResolve y =
    PartialResolve $ Map.unionWith earlier x y
  UniqueLocal x <> _ = UniqueLocal x
  _ <> UniqueLocal x = UniqueLocal x
  stimes = stimesIdempotent

resolvedUnique :: NameR scope -> Error.AmbiguousOrigin -> PartialResolve scope
resolvedUnique name origin = PartialResolve (Map.singleton name origin)

viewUniqueResolve :: PartialResolve scope -> Either [Error.AmbiguousOrigin] (NameR scope)
viewUniqueResolve = \case
  PartialResolve m
    | [name] <- Map.keys m -> Right name
    | otherwise -> Left (Map.elems m)
  UniqueLocal name -> Right name

-- | A map from user written names to the globally unique renamed version.
newtype Bindings scope = Bindings (NameMapG Written scope (PartialResolve scope))
  deriving newtype (Monoid)

instance Semigroup (Bindings scope) where
  Bindings x <> Bindings y = Bindings $ Map.unionWith (<>) x y
  stimes = stimesIdempotentMonoid

-- | Gives access to the underlying map of a @Bindings' scope@ value.
--
-- The type is intentionally more restricted. We usually don't want to replace
-- the whole map with a differently scoped version. This should also improve
-- type inference.
_Bindings :: Lens' (Bindings scope) (NameMapG Written scope (PartialResolve scope))
_Bindings = coerced
{-# INLINE _Bindings #-}

data RenameEnv = RenameEnv
  { rnTyVars :: !(Bindings Types),
    rnProgVars :: !(Bindings Values)
  }
  deriving stock (Generic)

instance Monoid RenameEnv where
  mempty = RenameEnv mempty mempty

instance Semigroup RenameEnv where
  e1 <> e2 =
    RenameEnv
      { rnTyVars = rnTyVars e1 <> rnTyVars e2,
        rnProgVars = rnProgVars e1 <> rnProgVars e2
      }

instance ScopeIndexed RenameEnv Bindings where
  typesScopeL = field @"rnTyVars"
  valuesScopeL = field @"rnProgVars"

moduleImportsEnv :: MonadErrors m => Globals -> Module x -> m RenameEnv
moduleImportsEnv globals = resolveImports globals . moduleImports

resolveImports ::
  MonadErrors m => Globals -> [Located Import] -> m RenameEnv
resolveImports modules =
  getAp . foldMap' (Ap . resolveImport modules)

-- | Resolve a single 'Import' to the starting 'RenameEnv'.
resolveImport ::
  MonadErrors m => Globals -> Located Import -> m RenameEnv
resolveImport modules stmt = getAp do
  -- At the moment the driver diagnoses unresolvable imports. Therefore here we
  -- fail silently.
  flip foldMap (HM.lookup (foldL importTarget stmt) modules) $
    Ap . selectedRenameEnv stmt

-- | Apply an 'ImportSelection' to a 'ModuleMap'. Essentially this restricts
-- the 'ModuleMap' and/or applies renamings. However this function does more
-- work:
--
-- * Unresolvable identifiers are diagnosed.
-- * It returns a complete 'RenameEnv'. The names contained inside have been
-- adjusted based on the 'importQualifier'.
selectedRenameEnv ::
  forall m.
  MonadErrors m =>
  Located Import ->
  ModuleMap ->
  m RenameEnv
selectedRenameEnv stmt mm =
  case foldL importSelection stmt of
    ImportAll allLoc hides renames -> do
      -- The allSet contains all identifiers which are not hidden.
      let allSet = allItems allLoc \itemKey -> not $ HM.member itemKey hides
      -- Add all the renamed items on top of the `allSet`.
      getAp $ pure allSet <> HM.foldMapWithKey (coerce addItem) renames
    ImportOnly renames ->
      getAp $ HM.foldMapWithKey (coerce addItem) renames
  where
    nameHereQ :: Unqualified -> NameW scope
    nameHereQ = Name (foldL importQualifier stmt)

    singleBinding :: forall scope. Pos -> Unqualified -> NameR scope -> Bindings scope
    singleBinding loc unq nameR = do
      Bindings . Map.singleton (nameHereQ unq) $
        resolvedUnique
          (nameR & nameWrittenL .~ nameHereQ unq)
          (Error.AmbiguousImport loc (foldL importTarget stmt))

    allItems :: Pos -> (ImportKey -> Bool) -> RenameEnv
    allItems allLoc include = do
      let item :: forall scope. SingI scope => Unqualified -> NameR scope -> Bindings scope
          item unqualified nameR =
            mguard
              (include (demote @scope, unqualified))
              (singleBinding allLoc unqualified nameR)
      RenameEnv
        { rnTyVars = HM.foldMapWithKey item (modMapTypes mm ^. _TopLevels),
          rnProgVars = HM.foldMapWithKey item (modMapValues mm ^. _TopLevels)
        }

    addItem :: ImportKey -> Located Unqualified -> m RenameEnv
    addItem (scope, nameHere) item@(_ :@ nameThere) = withSomeSing scope \sscope -> do
      let resolvedItem = mm ^. scopeL' sscope . _TopLevels . L.hashAt nameThere
      when (isNothing resolvedItem) do
        addError $
          Error.unknownImportItem
            (pos stmt)
            (foldL importTarget stmt)
            scope
            item
      pure $ flip foldMap resolvedItem \nameThereR ->
        mempty & scopeL' sscope .~ singleBinding (pos item) nameHere nameThereR

type RnM = ValidateT DErrors (ReaderT (ModuleMap, RenameEnv) Fresh)

instance SynTraversal RnM Parse Rn where
  typeVariable _ x = fmap (T.Var x) . lookupName Error.Var x
  valueVariable _ x = fmap (E.Var x) . lookupName Error.Var x
  bind _ vs = withBindings \f -> traverse f vs

  useConstructor _ loc w = case singByProxy w of
    -- Special check for value constructors: We have to resolve `(,)` to
    -- `conPair`.
    SValues | w == nameWritten Builtin.conPair -> pure Builtin.conPair
    _ -> lookupName Error.Con loc w

lookupName :: SingI scope => Error.NameKind -> Pos -> NameW scope -> RnM (NameR scope)
lookupName kind loc w = do
  resolve <- asks . view $ _2 . scopeL . _Bindings . at w
  case viewUniqueResolve <$> resolve of
    Nothing ->
      fatalError $ Error.unboundName loc kind w
    Just (Right r) ->
      pure r
    Just (Left choices) ->
      fatalError $ Error.ambiguousUsage loc kind w choices

bindingParams :: D.Params PStage -> (D.Params RnStage -> RnM a) -> RnM a
bindingParams params = withBindings \f ->
  traverse (bitraverse (traverse f) pure) params

bindingANames ::
  Traversable f => f (ANameG Written) -> (f (ANameG Resolved) -> RnM a) -> RnM a
bindingANames vs = withBindings \bind ->
  traverse (bitraverse bind bind) vs
{-# INLINEABLE bindingANames #-}

withBindings ::
  (forall f. Applicative f => (forall s. SingI s => PName s -> f (RnName s)) -> f a) ->
  (a -> RnM b) ->
  RnM b
withBindings f k = do
  let bind :: SingI s => PName s -> StateT RenameEnv Fresh (RnName s)
      bind v = do
        v' <- lift $ freshResolved v
        scopeL . _Bindings %= Map.insert v (UniqueLocal v')
        pure v'
  (a, binds) <- lift $ lift $ runStateT (f bind) mempty

  -- It is important that `binds` appears on the LEFT side of the `(<>)`
  -- operator! When unioning the underlying maps prefer values from the left
  -- operand. The new bindings in `binds` have to shadow/replace older
  -- bindings.
  local (fmap (binds <>)) (k a)

newtype RenameExtra = RenameExtra (forall a. (RnModule -> RnM a) -> Either DErrors a)

type RenameResult a = (ModuleMap, Globals -> Validate DErrors a)

renameSimple ::
  Globals -> (Globals -> Validate DErrors RenameExtra) -> Either DErrors RnModule
renameSimple globals resolve =
  runValidate (resolve globals) >>= \(RenameExtra f) -> f pure

renameModule :: ModuleName -> PModule -> RenameResult RnModule
renameModule name m =
  ( moduleMap,
    \g -> do
      RenameExtra extra <- rename g
      let errOrA = extra pure
      either refute pure errOrA
  )
  where
    (moduleMap, rename) = renameModuleExtra name m

renameModuleExtra :: ModuleName -> PModule -> RenameResult RenameExtra
renameModuleExtra = continueRenameExtra emptyModuleMap

-- | Given a partial module map (base map) this function “continues” the rename
-- of the given model in the sense that any top-level identifiers are first
-- looked for in the base map before a fresh name is generated.
--
-- This allows to refer to top-level identifiers before the whole module is
-- renamed. Also, it gives you stable identifiers you can generate which are
-- valid after renaming.
continueRenameExtra :: ModuleMap -> ModuleName -> PModule -> RenameResult RenameExtra
continueRenameExtra baseMap moduleName m =
  -- Renaming traverses the module top-levels twice. Overall this is acceptable
  -- but it might be possible using laziness and recrursive definitions to
  -- reduce it to one traversal.
  -- The difficult part, however, is to ensure that it is not possible to
  -- get stuck in an infinite recursion when some part is to strict.
  (toplevels, renameBodies)
  where
    firstId = do
      let idsOf = views (_TopLevels . traverse . nameResolvedIdL) DL.singleton
      case DL.toList $ idsOf (modMapTypes baseMap) <> idsOf (modMapValues baseMap) of
        [] -> firstResolvedId
        ids -> nextResolvedId $ maximum ids
    ((toplevels, localsEnv), nextRid) =
      moduleTopLevels baseMap m
        & unFresh
        & flip runReaderT moduleName
        & flip runState firstId
    renameBodies globals = do
      importsEnv <- moduleImportsEnv globals m
      let baseEnv = localsEnv <> importsEnv
      pure $ RenameExtra \k ->
        (doRename m >>= k)
          & runValidateT
          & flip runReaderT (toplevels, baseEnv)
          & unFresh
          & flip runReaderT moduleName
          & flip evalState nextRid

moduleTopLevels :: ModuleMap -> PModule -> Fresh (ModuleMap, RenameEnv)
moduleTopLevels baseMap m = do
  let entry ::
        (SingI scope, Position a) =>
        NameW scope ->
        a ->
        Fresh ((Unqualified, NameR scope), PartialResolve scope)
      entry nameW decl = do
        -- Only generate a fresh name if there isn't already a resolved version
        -- in `baseMap`.
        nameR <- case baseMap ^. scopeL . _TopLevels . hashAt (nameUnqualified nameW) of
          Nothing -> freshResolved nameW
          Just n -> pure n
        pure
          ( (nameUnqualified nameW, nameR),
            resolvedUnique nameR $ Error.AmbiguousDefine $ pos decl
          )
  typs <- Map.traverseWithKey entry $ moduleTypes m
  vals <- Map.traverseWithKey entry $ moduleValues m
  sigs <- Map.traverseWithKey entry $ moduleSigs m
  pure
    ( ModuleMap
        { modMapTypes =
            TopLevels . HM.fromList $
              fst <$> Map.elems typs,
          modMapValues =
            TopLevels . HM.fromList $
              (fst <$> Map.elems sigs) ++ (fst <$> Map.elems vals)
        },
      RenameEnv
        { rnTyVars = Bindings $ fmap snd typs,
          rnProgVars = Bindings $ fmap snd (vals <> sigs)
        }
    )

doRename :: PModule -> RnM RnModule
doRename m = do
  typs <- renameGlobalNameMap renameTypeDecl (moduleTypes m)
  sigs <- renameGlobalNameMap renameSigDecl (moduleSigs m)
  vals <-
    renameGlobalNameMap
      (bitraverse renameConDecl renameValDecl)
      (moduleValues m)
  pure
    Module
      { moduleTypes = typs,
        moduleValues = vals,
        moduleSigs = sigs,
        moduleImports = moduleImports m
      }

renameSyntax :: SynTraversable (s Parse) Parse (s Rn) Rn => s Parse -> RnM (s Rn)
renameSyntax = traverseSyntaxBetween (Proxy @Parse) (Proxy @Rn)

renameGlobalNameMap ::
  SingI scope =>
  (a -> RnM a') ->
  NameMapG Written scope a ->
  RnM (NameMapG Resolved scope a')
renameGlobalNameMap rn m = do
  tls <- asks fst
  fmap Map.fromList . sequenceA $
    [ (nameR,) <$> rn a
      | (nameUnqualified -> u, a) <- Map.toList m,
        nameR <- tls ^.. scopeL . _TopLevels . hashAt u . traverse
    ]

renameTypeDecl :: D.TypeDecl Parse -> RnM (D.TypeDecl Rn)
renameTypeDecl = \case
  D.AliasDecl x alias ->
    D.AliasDecl x <$> renameAlias alias
  D.DataDecl x decl ->
    D.DataDecl x <$> renameNominal renameSyntax decl
  D.ProtoDecl x decl ->
    D.ProtoDecl x <$> renameNominal renameSyntax decl

renameAlias :: D.TypeAlias Parse -> RnM (D.TypeAlias Rn)
renameAlias alias = bindingParams (D.aliasParams alias) \ps -> do
  ty <- renameSyntax (D.aliasType alias)
  pure
    D.TypeAlias
      { aliasParams = ps,
        aliasType = ty,
        aliasKind = D.aliasKind alias
      }

renameNominal :: (a -> RnM b) -> D.TypeNominal PStage a -> RnM (D.TypeNominal RnStage b)
renameNominal f nom = bindingParams (D.nominalParams nom) \ps -> do
  cs <-
    renameGlobalNameMap
      (traverse (traverse f))
      (D.nominalConstructors nom)
  pure
    D.TypeNominal
      { nominalParams = ps,
        nominalConstructors = cs,
        nominalKind = D.nominalKind nom
      }

renameSigDecl :: D.SignatureDecl Parse -> RnM (D.SignatureDecl Rn)
renameSigDecl (D.SignatureDecl x ty) = D.SignatureDecl x <$> renameSyntax ty

renameConDecl :: D.ConstructorDecl Parse -> RnM (D.ConstructorDecl Rn)
renameConDecl = \case
  D.DataCon x parent params mul items -> do
    parentR <- resolveParent parent
    (params', items') <- bindingParams params \params' ->
      (params',) <$> traverse renameSyntax items
    pure $ D.DataCon x parentR params' mul items'
  D.ProtocolCon x parent params items -> do
    parentR <- resolveParent parent
    (params', items') <- bindingParams params \params' ->
      (params',) <$> traverse renameSyntax items
    pure $ D.ProtocolCon x parentR params' items'
  where
    resolveParent p =
      asks . view $
        _1
          . scopeL
          . _TopLevels
          . hashAt (nameUnqualified p)
          . to (fromMaybe $ error $ "DataCon parent name not found: " ++ pprName p)

renameValDecl :: D.ValueDecl Parse -> RnM (D.ValueDecl Rn)
renameValDecl vd =
  bindingANames (Compose $ D.valueParams vd) \(Compose ps) -> do
    t <- renameSyntax (D.valueType vd)
    e <- renameSyntax (D.valueBody vd)
    pure vd {D.valueParams = ps, D.valueType = t, D.valueBody = e}
