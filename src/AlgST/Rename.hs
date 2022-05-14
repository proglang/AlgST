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

module AlgST.Rename
  ( RnM,
    RenameEnv (..),
    runRename,
    withRenamedModule,
    Rn,
    RnExp,
    RnBind,
    RnCaseMap,
    RnModule,
    RnType,
    renameSyntax,
    renameModule,
    bindingParams,

    -- * Internals
    etaRnM,
  )
where

import AlgST.Parse.Phase
import AlgST.Rename.Fresh
import AlgST.Rename.Phase
import AlgST.Syntax.Decl qualified as D
import AlgST.Syntax.Expression qualified as E
import AlgST.Syntax.Name
import AlgST.Syntax.Program
import AlgST.Syntax.Traversal
import AlgST.Syntax.Type qualified as T
import AlgST.Util.Lenses
import Control.Applicative
import Control.Monad.Cont
import Control.Monad.Eta
import Control.Monad.Reader
import Control.Monad.State.Strict
import Data.Bitraversable
import Data.Functor.Compose
import Data.Generics.Lens.Lite
import Data.Map.Strict qualified as Map
import Data.Maybe
import Data.Singletons
import Data.Traversable
import GHC.Generics (Generic)
import Lens.Family2
import Lens.Family2.State.Strict
import Lens.Family2.Stock qualified as L
import Prelude hiding (lookup)

-- | A map from the user written name to the renamed version.
newtype Bindings s = Bindings (NameMap s (RnName s))
  deriving newtype (Monoid, Semigroup)

-- | Gives access to the underlying map of a @'Bindings' s@ value.
--
-- The type is intentionally more restricted. We usually don't want to replace
-- the whole map with a differently scoped version. This should also improve
-- type inference.
_Bindings :: Lens' (Bindings s) (NameMap s (RnName s))
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

varMapL :: forall s. SingI s => Lens' RenameEnv (Bindings s)
varMapL = scopeL @s
{-# INLINE varMapL #-}

type RnM = ReaderT RenameEnv Fresh

instance SynTraversal RnM Parse Rn where
  typeVariable _ x = fmap (T.Var x) . lookup
  valueVariable _ x = fmap (E.Var x) . lookup
  useConstructor _ = pure
  bind _ = bindingAll

runRename :: RnM a -> Fresh a
runRename = flip runReaderT mempty

withRenamedModule :: PModule -> (RnModule -> RnM a) -> Fresh a
withRenamedModule p f = runRename $ renameModule p >>= f

-- | Binds all variables traversed over in @f@. If there are duplicate names an
-- error will be emitted at the provided location.
bindingAll :: (Traversable t, SingI s) => t (RnName s) -> (t (RnName s) -> RnM a) -> RnM a
bindingAll vs = withBindings \x -> traverse x vs
{-# INLINEABLE bindingAll #-}

bindingAllPTVars :: Traversable f => f AName -> (f AName -> RnM a) -> RnM a
bindingAllPTVars vs = withBindings \bind ->
  traverse (bitraverse bind bind) vs
{-# INLINEABLE bindingAllPTVars #-}

withBindings ::
  (forall f. Applicative f => (forall s. SingI s => RnName s -> f (RnName s)) -> f a) ->
  (a -> RnM b) ->
  RnM b
withBindings f k = etaRnM do
  let bind :: SingI s => RnName s -> StateT RenameEnv Fresh (RnName s)
      bind v = do
        v' <- lift $ freshResolved v
        varMapL . _Bindings %= Map.insert v v'
        pure v'
  (a, binds) <- lift $ runStateT (f bind) mempty

  -- It is important that `binds` appears on the LEFT side of the `(<>)`
  -- operator! When unioning the underlying maps prefer values from the left
  -- operand. The new bindings in `binds` have to shadow/replace older
  -- bindings.
  local (binds <>) (k a)
{-# INLINE withBindings #-}

-- | @lookup v@ looks for a binding for @v@ and returns the renamed
-- variable.
--
-- In case the variable is unbound it is assumed to be a global definition.
-- Diagnosing this case is not considered the renamer's responsibility.
--
-- TODO: Should diagnosing unbound globals be part of the renamer? Then there
-- could be one place at which "did you mean ..." hints could be generated.
lookup :: SingI s => RnName s -> RnM (RnName s)
lookup v = do
  env <- ask
  pure $ fromMaybe v $ env ^. varMapL . _Bindings . L.at' v

renameModule :: Module Parse -> RnM (Module Rn)
renameModule p = do
  rnTypes <- traverse renameTypeDecl (moduleTypes p)
  rnValues <- traverse (bitraverse renameConDecl renameValueDecl) (moduleValues p)
  rnSigs <- traverse renameSignature (moduleSigs p)
  pure
    Module
      { moduleTypes = rnTypes,
        moduleValues = rnValues,
        moduleSigs = rnSigs,
        -- In theory the imports should not be needed any more after this
        -- stage. Let's just keep them around anyways unless we have a good
        -- reason to throw them out.
        moduleImports = moduleImports p
      }

renameSyntax :: SynTraversable (s Parse) Parse (s Rn) Rn => s Parse -> RnM (s Rn)
renameSyntax = traverseSyntaxBetween (Proxy @Parse) (Proxy @Rn)

renameSignature :: D.SignatureDecl Parse -> RnM (D.SignatureDecl Rn)
renameSignature (D.SignatureDecl x ty) = D.SignatureDecl x <$> renameSyntax ty

renameValueDecl :: D.ValueDecl Parse -> RnM (D.ValueDecl Rn)
renameValueDecl vd =
  bindingAllPTVars (Compose $ D.valueParams vd) \(Compose ps) -> etaRnM do
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

renameNominal :: (a -> RnM b) -> D.TypeNominal PStage a -> RnM (D.TypeNominal RnStage b)
renameNominal f nom = bindingParams (D.nominalParams nom) \ps -> do
  cs <- D.traverseConstructors (const f) (D.nominalConstructors nom)
  pure
    D.TypeNominal
      { nominalParams = ps,
        nominalConstructors = cs,
        nominalKind = D.nominalKind nom
      }

bindingParams :: D.Params PStage -> (D.Params RnStage -> RnM a) -> RnM a
bindingParams params f =
  etaRnM
    let (ps, ks) = unzip params
     in bindingAll (Compose ps) \(Compose ps') -> f (zip ps' ks)

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
etaRnM = etaReaderT . mapReaderT etaFresh
{-# INLINE etaRnM #-}
