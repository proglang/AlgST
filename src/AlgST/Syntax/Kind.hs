{-# LANGUAGE BinaryLiterals #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE PatternSynonyms #-}

module AlgST.Syntax.Kind
  ( -- * Kinds
    Basic (..),
    Multiplicity (..),
    Kind (Kind, TL, TU, SL, SU, ML, MU, P),
    relocate,

    -- ** Operations
    multiplicity,
    (<=?),
    leastUpperBound,

    -- * Bindings
    Bind (..),
  )
where

import AlgST.Syntax.Name
import Language.Haskell.TH.Syntax (Lift)
import Syntax.Base

data Basic = Session | Message | Top
  -- Ordering is important for correctness of the subkind check (<=?)!
  deriving (Eq, Ord, Lift)

instance Show Basic where
  show Session = "S"
  show Message = "M"
  show Top     = "T"

data Kind
  = Kind !Pos !Basic !Multiplicity
  | P !Pos
  deriving (Lift)

instance Show Kind where
  show (P  _) = "P"
  show (TU _) = "TU"
  show (TL _) = "TL"
  show (SU _) = "SU"
  show (SL _) = "SL"
  show (MU _) = "MU"
  show (ML _) = "ML"

instance Position Kind where
  pos (Kind p _ _) = p
  pos (P p) = p

instance Eq Kind where
  Kind _ b m == Kind _ b' m' = b == b' && m == m'
  P _ == P _ = True
  _ == _ = False

{- ORMOLU_DISABLE -}
pattern TL, TU, SL, SU, ML, MU :: Pos -> Kind
pattern TL p = Kind p Top Lin
pattern TU p = Kind p Top Un
pattern ML p = Kind p Message Lin
pattern MU p = Kind p Message Un
pattern SL p = Kind p Session Lin
pattern SU p = Kind p Session Un
{- ORMOLU_ENABLE -}

{-# COMPLETE TL, TU, SL, SU, ML, MU, P #-}

relocate :: Kind -> Pos -> Kind
relocate (Kind _ b m) p = Kind p b m
relocate (P _) p = P p

infix 4 <=?

-- | Implements the partial order on kinds corresponding to the subkinding relationship.
(<=?) :: Kind -> Kind -> Bool
Kind _ b m <=? Kind _ b' m' =
  b <= b' && m <= m'
_ <=? P _ =
  True
P _ <=? Kind {} =
  False

-- | Extracts the kind's multiplicity information if there is any attached.
--
-- >>> multiplicity (TL defaultPos)
-- Just L
-- >>> multiplicity (P defaultPos)
-- Nothing
multiplicity :: Kind -> Maybe Multiplicity
multiplicity (P _) = Nothing
multiplicity (Kind _ _ m) = Just m

-- | Calculates the least upper bound of two kinds.
leastUpperBound :: Kind -> Kind -> Kind
leastUpperBound (P p) _ = P p
leastUpperBound _ (P p) = P p
leastUpperBound (Kind p b m) (Kind _ b' m') = Kind p (max b b') (max m m')

-- | > Bind _ v k a               ~ ∀(v:k). a
--   >                            ~ \[v:k] -> a
data Bind a = Bind Pos !TypeVar !Kind a
  deriving (Lift)

instance Position (Bind a) where
  pos (Bind p _ _ _) = p
