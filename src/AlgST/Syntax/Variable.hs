{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module AlgST.Syntax.Variable
  ( ProgVar,
    TypeVar,
    pattern UserNamed,
    isWild,
    PTVar,
    Variable (..),
    liftVar,
    liftVarSet,
    liftVarMap,
    chooseVar,
    Base.mkVar,
    Base.Pos,
    Base.Position (..),
  )
where

import qualified Data.Char as C
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Type.Equality
import qualified Syntax.Base as Base
import Syntax.ProgramVariable
import Syntax.TypeVariable

-- | Either a 'TypeVar' or a 'ProgVar'.
type PTVar = Either ProgVar TypeVar

class (Show v, Ord v, Base.Variable v) => Variable v where
  ptEvidence :: Either (v :~: ProgVar) (v :~: TypeVar)

instance Variable ProgVar where
  ptEvidence = Left Refl

instance Variable TypeVar where
  ptEvidence = Right Refl

liftVar :: forall v. Variable v => v -> PTVar
liftVar = chooseVar @v Left Right
{-# INLINE liftVar #-}

liftVarSet :: Variable v => Set.Set v -> Set.Set PTVar
liftVarSet = Set.mapMonotonic liftVar

liftVarMap :: Variable v => Map.Map v a -> Map.Map PTVar a
liftVarMap = Map.mapKeysMonotonic liftVar

chooseVar :: forall v r. Variable v => (v ~ ProgVar => r) -> (v ~ TypeVar => r) -> r
chooseVar p t = either (\Refl -> p) (\Refl -> t) (ptEvidence @v)
{-# INLINE chooseVar #-}

instance Show ProgVar where
  show = showVar

instance Show TypeVar where
  show = showVar

-- | @showVar@ takes the internal representation but drops any potential unique
-- prefix. This should be aligned with the implementations of 'Base.mkNewVar'.
showVar :: Base.Variable v => v -> String
showVar = dropWhile (\c -> C.isDigit c || c == '#') . Base.intern

pattern UserNamed :: Variable a => String -> a
pattern UserNamed s <- (showVar -> s)

isWild :: Variable v => v -> Bool
isWild (UserNamed "_") = True
isWild _ = False
