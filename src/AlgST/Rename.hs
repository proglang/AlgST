{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
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
    bindingParams,

    -- * Internals
    etaRnM,
  )
where

import AlgST.Parse.Phase
import AlgST.Syntax.Decl qualified as D
import AlgST.Syntax.Expression qualified as E
import AlgST.Syntax.Program
import AlgST.Syntax.Traversal
import AlgST.Syntax.Type qualified as T
import AlgST.Syntax.Variable
import Control.Applicative
import Control.Category ((>>>))
import Control.Monad.Cont
import Control.Monad.Eta
import Control.Monad.Reader
import Control.Monad.State.Strict
import Data.Bitraversable
import Data.Map.Strict qualified as Map
import Data.Maybe
import Data.Proxy
import Data.Traversable
import Lens.Family2
import Lens.Family2.State.Strict
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
    rnProgVars :: !(Bindings ProgVar)
  }

emptyEnv :: RenameEnv
emptyEnv = RenameEnv mempty mempty

rnTyVarsL :: Lens' RenameEnv (Bindings TypeVar)
rnTyVarsL = lens rnTyVars \env vs -> env {rnTyVars = vs}
{-# INLINE rnTyVarsL #-}

rnProgVarsL :: Lens' RenameEnv (Bindings ProgVar)
rnProgVarsL = lens rnProgVars \env vs -> env {rnProgVars = vs}
{-# INLINE rnProgVarsL #-}

type RnSt = Int

-- | The monad stack used during renaming.
--
-- Try to use it in an applicative way or with @ApplicativeDo@ enabled. This
-- will allow more errors to be gathered in one pass. See
-- [the documentation of @monad-validate@](https://hackage.haskell.org/package/monad-validate-1.2.0.0/docs/Control-Monad-Validate.html#t:ValidateT)
-- for more info.
type RnM =
  ReaderT RenameEnv (State RnSt)

instance VarTraversal RnM Parse where
  typeVariable = fmap Right . lookup
  programVariable = fmap Right . lookup

  bind :: (Traversable t, Variable v) => proxy Parse -> t v -> (t v -> RnM a) -> RnM a
  bind _ = bindingAll

runRename :: RnM a -> a
runRename = flip runReaderT emptyEnv >>> flip evalState 0

withRenamedProgram :: PProgram -> (RnProgram -> RnM a) -> a
withRenamedProgram p f = runRename $ renameProgram p >>= f

-- | Binds all variables traversed over in @f@. If there are duplicate names an
-- error will be emitted at the provided location.
bindingAll :: (Traversable f, Variable v) => f v -> (f v -> RnM a) -> RnM a
bindingAll vs = withBindings \x -> traverse x vs
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
        n <- lift $ get <* modify' (+ 1)
        let v' = mkNewVar n v
        varMapL . at' v .= Just v'
        pure v'
  (a, binds) <- runStateT (f bind) emptyEnv

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
-- variable. In case the variable is unbound it is assumed to be a global
-- definition. In case it is not the typechecker will emit an error.
lookup :: Variable v => v -> RnM v
lookup v = etaRnM do
  env <- ask
  pure $ fromMaybe v $ env ^. varMapL . at v

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
      (params', items') <- bindingParams params \params' ->
        (params',) <$> traverse renameSyntax items
      pure $ D.DataCon x parent params' mul items'
    D.ProtocolCon x parent params items -> do
      (params', items') <- bindingParams params \params' ->
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

renameTypeDecl :: D.TypeDecl Parse -> RnM (D.TypeDecl Rn)
renameTypeDecl =
  etaRnM . \case
    D.AliasDecl x alias ->
      D.AliasDecl x <$> renameAlias alias
    D.DataDecl x decl ->
      D.DataDecl x <$> renameNominal renameSyntax decl
    D.ProtoDecl x decl ->
      D.ProtoDecl x <$> renameNominal renameSyntax decl

etaRnM :: RnM a -> RnM a
etaRnM = etaReaderT . mapReaderT (etaStateT . seqStateT)
{-# INLINE etaRnM #-}
