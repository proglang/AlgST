module AlgST.Syntax.Operators where

import AlgST.Builtins.Names
import AlgST.Syntax.Name
import Data.Function
import Data.Map.Strict qualified as Map

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

data Info s = Info
  { opName :: !s,
    opAssoc :: !Associativity,
    opPrec :: !Precedence
  }

-- | A map from operator names (parenthesized and unparenthesized) to operator
-- 'Info'. The 'opName' fields always contain the parenthesized version.
--
-- Note that since this uses the operators' unqualified names as keys we
-- currently are not able to support user defined operators.
knownOperators :: Map.Map String (Info ProgVar)
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
        Info "<|" R PBackward
      ]

    opMap :: Info String -> Map.Map String (Info ProgVar)
    opMap op =
      let name1 = opName op
          name2 = operatorValueName (opName op)
          opNamed = op {opName = Builtin name2}
       in Map.empty
            & Map.insert name1 opNamed
            & Map.insert name2 opNamed

-- | Wraps a symbolic operator in parentheses.
operatorValueName :: String -> String
operatorValueName op = "(" ++ op ++ ")"
