{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module AlgST.Syntax.Module
  ( Module (..),
    moduleOrigins,
    emptyModule,
    mergeModules,
    importModule,
    withoutDefinitions,
    TypesMap,
    ValuesMap,
    SignaturesMap,
    ForallX,

    -- * Imports
    Import (..),
    ImportSelection (..),
    ImportItem (..),
  )
where

import AlgST.Syntax.Decl qualified as D
import AlgST.Syntax.Expression qualified as E
import AlgST.Syntax.Name
import AlgST.Syntax.Type qualified as T
import Data.Kind qualified as Hs
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import GHC.Conc
import Instances.TH.Lift ()
import Language.Haskell.TH.Syntax (Lift)
import Lens.Family2

-- | Groups the @ForallX@ constraint synonym from "AlgST.Syntax.Decl",
-- "AlgST.Syntax.Type", and "AlgST.Syntax.Expression".
type ForallX (c :: Hs.Type -> Hs.Constraint) x =
  ( D.ForallDeclX c x,
    D.ForallConX c x,
    T.ForallX c x,
    E.ForallX c x
  )

data Import = Import
  { -- | Full name of the imported module.
    importTarget :: ModuleName,
    -- | The qualifier for imported identifiers. Can be empty (@ModuleName ""@)
    -- in which case names are imported unqualified.
    importQualifier :: ModuleName,
    importSelection :: ImportSelection
  }
  deriving stock (Show, Lift)

data ImportSelection
  = -- | Import all public definitions from this module and rename/hide
    -- identifiers as specified in the 'ImportItem's.
    ImportAll [ImportItem]
  | -- | Import only the names specified, potentially renaming imported names.
    ImportOnly [ImportItem]
  deriving stock (Show, Lift)

data ImportItem
  = ImportName Unqualified
  | ImportHide Unqualified
  | ImportRename Unqualified Unqualified
  deriving stock (Show, Lift)

data Module x = Module
  { moduleTypes :: !(TypesMap x),
    moduleValues :: !(ValuesMap x),
    moduleSigs :: !(SignaturesMap x),
    moduleImports :: [Import]
  }

deriving stock instance (ForallX Lift x) => Lift (Module x)

emptyModule :: Module x
emptyModule = Module Map.empty Map.empty Map.empty []

-- | A traversal over the 'Origin's of all declarations and signatures.
moduleOrigins ::
  (D.ForallDeclX D.Originated x, D.ForallConX D.Originated x) =>
  Traversal' (Module x) D.Origin
moduleOrigins f p = do
  types <- traverse (D.originL f) (moduleTypes p)
  values <- traverse (D.originL f) (moduleValues p)
  imports <- traverse (D.originL f) (moduleSigs p)
  pure
    Module
      { moduleTypes = types,
        moduleValues = values,
        moduleSigs = imports,
        moduleImports = []
      }

-- | Combines the types and values from two modules and returns the names of
-- conflicting types and values.
--
-- Note that merging modules after renaming or typechecking will usually
-- invalidate the guarantees made by these stages.
mergeModules :: Module x -> Module x -> (Module x, NameSet Types, NameSet Values)
mergeModules p1 p2 =
  ( Module
      { moduleTypes = moduleTypes p1 <> moduleTypes p2,
        moduleValues = moduleValues p1 <> moduleValues p2,
        moduleSigs = moduleSigs p1 <> moduleSigs p2,
        moduleImports = moduleImports p1 <> moduleImports p2
      },
    types1 `Set.intersection` types2,
    mconcat [Set.intersection x y | x <- [vals1, imp1], y <- [vals2, imp2]]
  )
  where
    imp1 = Map.keysSet (moduleSigs p1)
    imp2 = Map.keysSet (moduleSigs p2)
    vals1 = Map.keysSet (moduleValues p1)
    vals2 = Map.keysSet (moduleValues p2)
    types1 = Map.keysSet (moduleTypes p1)
    types2 = Map.keysSet (moduleTypes p2)

importModule :: Module x -> Module x
importModule p =
  cons
    `par` vals
    `pseq` p {moduleValues = cons, moduleSigs = vals}
  where
    cons = Map.mapMaybe (either (Just . Left) (const Nothing)) (moduleValues p)
    vals = Map.mapMaybe (either (const Nothing) (Just . valueSigDecl)) (moduleValues p)
    valueSigDecl vd = D.SignatureDecl (vd ^. D.originL) (D.valueType vd)

-- | @withoutDefinitions p1 p2@ removes all definitions from @p1@ which
-- also appear in @p2π /in the same field./
withoutDefinitions :: Module x -> Module y -> Module x
withoutDefinitions p1 p2 =
  Module
    { moduleTypes = moduleTypes p1 \\ moduleTypes p2,
      moduleValues = moduleValues p1 \\ moduleValues p2,
      moduleSigs = moduleSigs p1 \\ moduleSigs p2,
      moduleImports = moduleImports p1
    }
  where
    (\\) :: NameMap s v -> NameMap s v' -> NameMap s v
    (\\) = Map.difference

-- | Mapping between type names and the type declarations.
type TypesMap x = NameMap Types (D.TypeDecl x)

-- | Mapping between value names and their declaration, which is either a
-- constructor or a value/function binding.
type ValuesMap x = NameMap Values (Either (D.ConstructorDecl x) (D.ValueDecl x))

-- | Mapping between value/function names and their signatures.
type SignaturesMap x = NameMap Values (D.SignatureDecl x)