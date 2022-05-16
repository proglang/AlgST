{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}

module AlgST.Rename.Imports
  ( RenameEnv,
    resolveImport,
    resolveImports,
  )
where

import AlgST.Rename.Error (MonadErrors, addError)
import AlgST.Rename.Error qualified as Error
import AlgST.Syntax.Name
import AlgST.Syntax.Program
import AlgST.Util
import AlgST.Util.Lenses
import AlgST.Util.Lenses qualified as L
import Control.Monad
import Data.Coerce
import Data.Foldable
import Data.Generics.Lens.Lite
import Data.HashMap.Strict
import Data.HashMap.Strict qualified as HM
import Data.Map qualified as Map
import Data.Maybe
import Data.Monoid
import Data.Semigroup
import Data.Singletons
import GHC.Generics (Generic)
import Lens.Family2
import Syntax.Base

newtype TopLevels scope = TopLevels (HashMap Unqualified (NameR scope))

_TopLevels :: Lens' (TopLevels scope) (HashMap Unqualified (NameR scope))
_TopLevels = coerced
{-# INLINE _TopLevels #-}

-- | A @ModuleMap@ maps unqualified top level names of a module to the
-- corresponding globally-resolved name.
data ModuleMap = ModuleMap
  { modMapTypes :: !(TopLevels Types),
    modMapValues :: !(TopLevels Values)
  }
  deriving stock (Generic)

instance ScopeIndexed ModuleMap TopLevels where
  typesScopeL = field @"modMapTypes"
  valuesScopeL = field @"modMapValues"

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
newtype PartialResolve scope
  = PartialResolve (Map.Map (NameR scope) Error.AmbiguousOrigin)

instance Semigroup (PartialResolve scope) where
  PartialResolve x <> PartialResolve y =
    PartialResolve $ Map.unionWith earlier x y
  stimes = stimesIdempotent

pattern ResolvedUnique :: NameR scope -> Error.AmbiguousOrigin -> PartialResolve scope
pattern ResolvedUnique name origin <-
  PartialResolve (Map.toList -> [(name, origin)])
  where
    ResolvedUnique name origin = PartialResolve (Map.singleton name origin)

-- | A map from user written names to the globally unique renamed version.
newtype Bindings scope = Bindings (NameMap scope (PartialResolve scope))
  deriving newtype (Monoid)

instance Semigroup (Bindings scope) where
  Bindings x <> Bindings y = Bindings $ Map.unionWith (<>) x y
  stimes = stimesIdempotentMonoid

-- | Gives access to the underlying map of a @Bindings' scope@ value.
--
-- The type is intentionally more restricted. We usually don't want to replace
-- the whole map with a differently scoped version. This should also improve
-- type inference.
_Bindings :: Lens' (Bindings scope) (NameMap scope (PartialResolve scope))
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

resolveImports ::
  MonadErrors m => HashMap ModuleName ModuleMap -> [Located Import] -> m RenameEnv
resolveImports modules =
  getAp . foldMap' (Ap . resolveImport modules)

-- | Resolve a single 'Import' to the starting 'RenameEnv'.
resolveImport ::
  MonadErrors m => HashMap ModuleName ModuleMap -> Located Import -> m RenameEnv
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
    nameHereQ = Name (foldL importQualifier stmt)

    singleBinding loc unq nameR =
      Bindings . Map.singleton (nameHereQ unq) $
        ResolvedUnique
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
