{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module AlgST.Syntax.Program
  ( Program (..),
    programOrigins,
    emptyProgram,
    mergePrograms,
    importProgram,
    withoutProgramDefinitions,
    TypesMap,
    ValuesMap,
    SignaturesMap,
    ForallX,
  )
where

import Data.Bifunctor
import qualified Data.Kind as Hs
import Data.Map.Strict ((\\))
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Instances.TH.Lift ()
import Language.Haskell.TH.Syntax (Lift)
import Lens.Family2
import qualified AlgST.Syntax.Decl as D
import qualified AlgST.Syntax.Expression as E
import qualified AlgST.Syntax.Type as T
import Syntax.ProgramVariable (ProgVar)
import Syntax.TypeVariable (TypeVar)

-- | Groups the @ForallX@ constraint synonym from "AlgST.Syntax.Decl",
-- "AlgST.Syntax.Type", and "AlgST.Syntax.Expression".
type ForallX (c :: Hs.Type -> Hs.Constraint) x =
  ( D.ForallDeclX c x,
    D.ForallConX c x,
    T.ForallX c x,
    E.ForallX c x
  )

data Program x = Program
  { programTypes :: !(TypesMap x),
    programValues :: !(ValuesMap x),
    programImports :: !(SignaturesMap x)
  }

deriving stock instance (ForallX Lift x) => Lift (Program x)

emptyProgram :: Program x
emptyProgram = Program Map.empty Map.empty Map.empty

-- | A traversal over the 'Origin's of all declarations and signatures.
programOrigins ::
  (D.ForallDeclX D.Originated x, D.ForallConX D.Originated x) =>
  Traversal' (Program x) D.Origin
programOrigins f p = do
  types <- traverse (D.originL f) (programTypes p)
  values <- traverse (D.originL f) (programValues p)
  imports <- traverse (D.originL f) (programImports p)
  pure
    Program
      { programTypes = types,
        programValues = values,
        programImports = imports
      }

-- | Combines the types and values from two programs and returns the names of
-- conflicting types and values.
--
-- Note that merging programs after renaming or typechecking will usually
-- invalidate the guarantees made by these stages.
mergePrograms :: Program x -> Program x -> (Program x, Set.Set TypeVar, Set.Set ProgVar)
mergePrograms p1 p2 =
  ( Program
      { programTypes = programTypes p1 <> programTypes p2,
        programValues = programValues p1 <> programValues p2,
        programImports = programImports p1 <> programImports p2
      },
    types1 `Set.intersection` types2,
    mconcat [Set.intersection x y | x <- [vals1, imp1], y <- [vals2, imp2]]
  )
  where
    imp1 = Map.keysSet (programImports p1)
    imp2 = Map.keysSet (programImports p2)
    vals1 = Map.keysSet (programValues p1)
    vals2 = Map.keysSet (programValues p2)
    types1 = Map.keysSet (programTypes p1)
    types2 = Map.keysSet (programTypes p2)

importProgram :: Program x -> Program x
importProgram p =
  Program
    { programTypes = programTypes p,
      programValues = cons,
      programImports = vals
    }
  where
    (cons, vals) = Map.mapEither (bimap Left valueSigDecl) (programValues p)
    valueSigDecl vd = D.SignatureDecl (vd ^. D.originL) (D.valueType vd)

-- | @deleteProgramDefinitions p1 p2@ removes all definitions from @p1@ which
-- also appear in @p2π /in the same field./
withoutProgramDefinitions :: Program x -> Program y -> Program x
withoutProgramDefinitions p1 p2 =
  Program
    { programTypes = programTypes p1 \\ programTypes p2,
      programValues = programValues p1 \\ programValues p2,
      programImports = programImports p1 \\ programImports p2
    }

-- | Mapping between type names and the type declarations.
type TypesMap x = Map.Map TypeVar (D.TypeDecl x)

-- | Mapping between value names and their declaration, which is either a
-- constructor or a value/function binding.
type ValuesMap x = Map.Map ProgVar (Either (D.ConstructorDecl x) (D.ValueDecl x))

-- | Mapping between value/function names and their signatures.
type SignaturesMap x = Map.Map ProgVar (D.SignatureDecl x)
