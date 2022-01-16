{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module AlgST.Rename
  ( RnM,
    RenameEnv (..),
    emptyEnv,
    runRename,
    withRenamedProgram,
    Rn,
    RnExp,
    RnBind,
    RnCaseMap,
    RnProgram,
    RnType,
    renameSyntax,
    renameProgram,
    bindingParamsUnchecked,

    -- * Internals
    etaRnM,
  )
where

import AlgST.Parse.Phase
import qualified AlgST.Syntax.Decl as D
import qualified AlgST.Syntax.Expression as E
import AlgST.Syntax.Program
import AlgST.Syntax.Traversal
import qualified AlgST.Syntax.Type as T
import AlgST.Syntax.Variable
import AlgST.Util.ErrorMessage
import Control.Applicative
import Control.Category ((>>>))
import Control.Monad.Cont
import Control.Monad.Eta
import Control.Monad.Reader
import Control.Monad.State.Strict
import Control.Monad.Validate
import Data.Bifunctor
import Data.Bitraversable
import Data.DList.DNonEmpty (DNonEmpty)
import qualified Data.DList.DNonEmpty as DL
import Data.List.NonEmpty (NonEmpty)
import qualified Data.Map.Strict as Map
import Data.Proxy
import Data.Traversable
import Lens.Family2
import Lens.Family2.Stock
import Lens.Family2.Unchecked (lens)
import Syntax.Base hiding (Variable)
import Prelude hiding (lookup)

-- | The rename phase token is only an alias to the 'Parse' token. All
-- annotations are preserved but all bound variables are renamed to distinct
-- names.
type Rn = Parse

{- ORMOLU_DISABLE -}
type RnExp = E.Exp Rn
type RnBind = E.Bind Rn
type RnCaseMap = E.CaseMap Rn
type RnProgram = Program Rn
type RnType = T.Type Rn
{- ORMOLU_ENABLE -}

type Bindings v = Map.Map v v

data RenameEnv = RenameEnv
  { rnTyVars :: !(Bindings TypeVar),
    rnProgVars :: !(Bindings ProgVar),
    rnContext :: !PProgram
  }

emptyEnv :: PProgram -> RenameEnv
emptyEnv = RenameEnv mempty mempty

rnTyVarsL :: Lens' RenameEnv (Bindings TypeVar)
rnTyVarsL = lens rnTyVars \env vs -> env {rnTyVars = vs}
{-# INLINE rnTyVarsL #-}

rnProgVarsL :: Lens' RenameEnv (Bindings ProgVar)
rnProgVarsL = lens rnProgVars \env vs -> env {rnProgVars = vs}
{-# INLINE rnProgVarsL #-}

type Errors = DNonEmpty PosError

type RnSt = Int

-- | The monad stack used during renaming.
--
-- Try to use it in an applicative way or with @ApplicativeDo@ enabled. This
-- will allow more errors to be gathered in one pass. See
-- [the documentation of @monad-validate@](https://hackage.haskell.org/package/monad-validate-1.2.0.0/docs/Control-Monad-Validate.html#t:ValidateT)
-- for more info.
type RnM =
  ValidateT Errors (ReaderT RenameEnv (State RnSt))

instance VarTraversal RnM Parse where
  typeVariable = fmap Right <$> lookup unboundTypeVarError
  programVariable = fmap Right <$> lookup unboundProgVarError

  bind :: (Traversable t, Variable v) => proxy Parse -> t v -> (t v -> RnM a) -> RnM a
  bind _ = bindingAll

runRename :: PProgram -> RnM a -> Either (NonEmpty PosError) a
runRename prog =
  runValidateT
    >>> flip runReaderT (emptyEnv prog)
    >>> flip evalState 0
    >>> first DL.toNonEmpty

withRenamedProgram :: PProgram -> (RnProgram -> RnM a) -> Either (NonEmpty PosError) a
withRenamedProgram p f = runRename p $ renameProgram p >>= f

addError :: MonadValidate Errors m => PosError -> m ()
addError = dispute . DL.singleton

addFatalError :: MonadValidate Errors m => PosError -> m a
addFatalError = refute . DL.singleton

-- | Binds all variables traversed over in @f@. If there are duplicate names an
-- error will be emitted at the provided location.
bindingAll :: (Traversable f, Variable v) => f v -> (f v -> RnM a) -> RnM a
bindingAll vs = withBindings (`traverse` vs)
{-# INLINEABLE bindingAll #-}

bindingAllPTVars :: Traversable f => f PTVar -> (f PTVar -> RnM a) -> RnM a
bindingAllPTVars vs = withBindings \bind ->
  traverse (bitraverse bind bind) vs
{-# INLINEABLE bindingAllPTVars #-}

varMapL :: forall v. Variable v => Lens' RenameEnv (Bindings v)
varMapL = chooseVar @v rnProgVarsL rnTyVarsL
{-# INLINE varMapL #-}

withBindings ::
  (forall f. Applicative f => (forall v. Variable v => v -> f v) -> f a) ->
  (a -> RnM b) ->
  RnM b
withBindings f k = etaRnM do
  let bind :: Variable v => v -> StateT RenameEnv RnM v
      bind v = do
        env <- get
        if
            -- Error when a name is bound twice, except for holes "_", which
            -- may appear as often as one wants.
            | show v /= "_",
              Just sameV <- env ^. varMapL . at' v -> do
              addError $ nameBoundTwice v (pos sameV) (pos v)
              pure sameV

            -- Bind v and assign it a new unique.
            | otherwise -> do
              n <- lift $ get <* modify' (+ 1)
              let v' = mkNewVar n v
              modify' $ varMapL . at' v .~ Just v'
              pure v'

  ctxt <- asks rnContext
  (a, binds) <- runStateT (f bind) (emptyEnv ctxt)

  -- Don't use (<>~) here! (<>)/union on Data.Map prefers values from the left
  -- operand on duplicate keys. But the values from `binds` have to replace
  -- (shadow) the already known bindings.
  local
    ( rnTyVarsL %~ (rnTyVars binds <>)
        >>> rnProgVarsL %~ (rnProgVars binds <>)
    )
    (k a)
{-# INLINE withBindings #-}

-- | @lookup mkErr v@ looks for a binding for @v@ and returns the renamed
-- variable. In case the variable is unbound @mkErr v@ is added to the list of
-- errors.
lookup :: Variable v => (v -> PosError) -> v -> RnM v
lookup unboundError v = etaRnM do
  env <- ask
  case env ^. varMapL . at v of
    Nothing -> do
      when (not (boundInContext v (rnContext env))) do
        -- See [Note: unbound variables and non-fatal errors].
        addFatalError $ unboundError v
      pure v
    Just v' -> do
      pure v'

{-
[Note: unbound variables and non-fatal errors]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Producing a non-fatal error on unbound variables can lead to 'error' calls in
the typechecker. A non-fatal error means that monadic pipelines will continue
processing which is incorrect: the typechecker must only run when we can be
sure that the referenced variables exist.

Still, by way of the 'Validate' monad processing of the other branches of the
program will continue even if some variables are not bound.
-}

boundInContext :: forall v. Variable v => v -> PProgram -> Bool
boundInContext v =
  chooseVar @v
    (liftA2 (||) (Map.member v . programValues) (Map.member v . programImports))
    (Map.member v . programTypes)

renameProgram :: Program Parse -> RnM (Program Rn)
renameProgram p = do
  rnTypes <- traverse renameTypeDecl (programTypes p)
  rnValues <- traverse (bitraverse renameConDecl renameValueDecl) (programValues p)
  rnSigs <- traverse renameSignature (programImports p)
  pure
    Program
      { programTypes = rnTypes,
        programValues = rnValues,
        programImports = rnSigs
      }

renameSyntax :: VarTraversable (s Parse) Parse => s Parse -> RnM (s Rn)
renameSyntax = traverseVars @_ @Parse Proxy

renameSignature :: D.SignatureDecl Parse -> RnM (D.SignatureDecl Rn)
renameSignature (D.SignatureDecl x ty) = D.SignatureDecl x <$> renameSyntax ty

renameValueDecl :: D.ValueDecl Parse -> RnM (D.ValueDecl Rn)
renameValueDecl vd = bindingAllPTVars (D.valueParams vd) \ps -> etaRnM do
  t <- renameSyntax (D.valueType vd)
  e <- renameSyntax (D.valueBody vd)
  pure vd {D.valueParams = ps, D.valueType = t, D.valueBody = e}

renameConDecl :: D.ConstructorDecl Parse -> RnM (D.ConstructorDecl Rn)
renameConDecl =
  etaRnM . \case
    D.DataCon x parent params mul items -> do
      (params', items') <- bindingParamsUnchecked params \params' ->
        (params',) <$> traverse renameSyntax items
      pure $ D.DataCon x parent params' mul items'
    D.ProtocolCon x parent params items -> do
      (params', items') <- bindingParamsUnchecked params \params' ->
        (params',) <$> traverse renameSyntax items
      pure $ D.ProtocolCon x parent params' items'

renameAlias :: D.TypeAlias Parse -> RnM (D.TypeAlias Rn)
renameAlias alias = bindingParams (D.aliasParams alias) \ps -> do
  ty <- renameSyntax (D.aliasType alias)
  pure
    D.TypeAlias
      { aliasParams = ps,
        aliasType = ty,
        aliasKind = D.aliasKind alias
      }

renameNominal :: (a -> RnM b) -> D.TypeNominal a -> RnM (D.TypeNominal b)
renameNominal f nom = bindingParams (D.nominalParams nom) \ps -> do
  cs <- D.traverseConstructors (const f) (D.nominalConstructors nom)
  pure
    D.TypeNominal
      { nominalParams = ps,
        nominalConstructors = cs,
        nominalKind = D.nominalKind nom
      }

bindingParams :: D.Params -> (D.Params -> RnM a) -> RnM a
bindingParams params f =
  etaRnM
    let (ps, ks) = unzip params
     in bindingAll ps \ps' -> f (zip ps' ks)

-- | Like 'bindingParams' but does not generate any errors should there be
-- duplicate names.
--
-- This is used when renaming the items of constructors. Every constructor has
-- to bind the type's parameters but we don't want to generate the same errors
-- for each constructor. The errors are generated when renaming the declaration
-- as a whole.
bindingParamsUnchecked :: D.Params -> (D.Params -> RnM a) -> RnM a
bindingParamsUnchecked =
  runContT . traverse \(tv, k) -> fmap (,k) $ ContT $ bindOne @Rn Proxy tv

renameTypeDecl :: D.TypeDecl Parse -> RnM (D.TypeDecl Rn)
renameTypeDecl =
  etaRnM . \case
    D.AliasDecl x alias ->
      D.AliasDecl x <$> renameAlias alias
    D.DataDecl x decl ->
      D.DataDecl x <$> renameNominal renameSyntax decl
    D.ProtoDecl x decl ->
      D.ProtoDecl x <$> renameNominal renameSyntax decl

unboundProgVarError :: ProgVar -> PosError
unboundProgVarError pv =
  PosError
    (pos pv)
    [ Error "Unbound variable",
      Error pv
    ]

unboundTypeVarError :: TypeVar -> PosError
unboundTypeVarError tv =
  PosError
    (pos tv)
    [ Error "Unbound type variable",
      Error tv
    ]

nameBoundTwice :: forall v. Variable v => v -> Pos -> Pos -> PosError
nameBoundTwice name p1 p2 =
  PosError
    (min p1 p2)
    [ Error "Conflicting definitions for",
      chooseVar @v Error Error name,
      ErrLine,
      Error "Bound at:",
      Error (min p1 p2),
      ErrLine,
      Error "         ",
      Error (max p1 p2)
    ]

etaRnM :: RnM a -> RnM a
etaRnM = etaValidateT . mapValidateT (etaReaderT . mapReaderT (etaStateT . seqStateT))
{-# INLINE etaRnM #-}
