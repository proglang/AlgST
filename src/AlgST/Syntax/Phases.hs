module AlgST.Syntax.Phases where

import Data.Kind

type Phase = Type

type CAll = (Type -> Constraint) -> Phase -> Constraint

type CSame = Phase -> Phase -> Constraint
