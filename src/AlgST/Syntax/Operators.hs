module AlgST.Syntax.Operators where

import Data.Function
import qualified Data.Map.Strict as Map

data Precedence
  = -- | > (<|)
    PBackward
  | -- | > (|>)
    PForward
  | -- | > (||)
    POr
  | -- | > (&&)
    PAnd
  | -- | > (==), (<=), …
    PCmp
  | -- | > (+), (-)
    PAddSub
  | -- | > (*), (/)
    PMulDiv
  deriving (Eq, Ord, Enum, Bounded, Show)

data Associativity = L | R | NA
  deriving (Eq)

data Info = Info
  { opName :: !String,
    opAssoc :: !Associativity,
    opPrec :: !Precedence
  }

-- | A map from operator names (parenthesized and unparenthesized) to operator
-- 'Info'. The 'opName' fields always contain the parenthesized version.
knownOperators :: Map.Map String Info
knownOperators = Map.unions (opMap <$> ops)
  where
    ops =
      [ Info "||" L POr,
        Info "&&" L PAnd,
        Info "<" NA PCmp,
        Info ">" NA PCmp,
        Info "<=" NA PCmp,
        Info ">=" NA PCmp,
        Info "==" NA PCmp,
        Info "/=" NA PCmp,
        Info "+" L PAddSub,
        Info "-" L PAddSub,
        Info "*" L PMulDiv,
        Info "/" L PMulDiv,
        Info "%" L PMulDiv,
        Info "|>" L PForward,
        Info "<|" R PBackward,
        Info "<&>" NA PBackward -- ???
      ]

    opMap :: Info -> Map.Map String Info
    opMap op =
      let op' = op {opName = operatorValueName (opName op)}
       in Map.empty
            & Map.insert (opName op) op'
            & Map.insert (opName op') op'

-- | Wraps a symbolic operator in parentheses.
operatorValueName :: String -> String
operatorValueName op = "(" ++ op ++ ")"
