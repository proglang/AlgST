{-# LANGUAGE BinaryLiterals #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE PatternSynonyms #-}

module AlgST.Syntax.Kind
  ( -- * Kinds
    Basic (..),
    Multiplicity (..),
    Kind (Kind, TL, TU, SL, SU, ML, MU, P),

    -- ** Operations
    multiplicity,
    leastUpperBound,

    -- * Bindings
    Bind (..),
  )
where

import AlgST.Syntax.Name
import AlgST.Syntax.Pos
import AlgST.Util.PartialOrd
import Control.Applicative
import Language.Haskell.TH.Syntax (Lift)
import Text.Read

data Multiplicity = Un | Lin
  -- Ordering is important for correctness of the subkind check (<=?)!
  deriving (Eq, Ord, Lift)

data Basic = Session | Message | Top
  -- Ordering is important for correctness of the subkind check (<=?)!
  deriving stock (Eq, Ord, Lift)

instance Show Basic where
  show Session = "S"
  show Message = "M"
  show Top = "T"

data Kind
  = Kind !Basic !Multiplicity
  | P
  deriving stock (Eq, Lift)

instance Show Kind where
  show P = "P"
  show TU = "TU"
  show TL = "TL"
  show SU = "SU"
  show SL = "SL"
  show MU = "MU"
  show ML = "ML"

instance Read Kind where
  readPrec =
    lexP >>= \case
      Ident "P" -> pure P
      Ident "T" -> pure TL
      Ident "TL" -> pure TL
      Ident "TU" -> pure TU
      Ident "S" -> pure SL
      Ident "SL" -> pure SL
      Ident "SU" -> pure SU
      Ident "M" -> pure ML
      Ident "ML" -> pure ML
      Ident "MU" -> pure MU
      _ -> empty

  readListPrec = readListPrecDefault

{- ORMOLU_DISABLE -}
pattern TL, TU, SL, SU, ML, MU :: Kind
pattern TL = Kind Top Lin
pattern TU = Kind Top Un
pattern ML = Kind Message Lin
pattern MU = Kind Message Un
pattern SL = Kind Session Lin
pattern SU = Kind Session Un
{- ORMOLU_ENABLE -}

{-# COMPLETE TL, TU, SL, SU, ML, MU, P #-}

-- | Kinds are partially ordered corresponding to the subkinding relationship.
instance PartialOrd Kind where
  Kind b m <=? Kind b' m' =
    b <= b' && m <= m'
  _ <=? P =
    True
  P <=? Kind _ _ =
    False

-- | Extracts the kind's multiplicity information if there is any attached.
--
-- >>> multiplicity (TL defaultPos)
-- Just L
-- >>> multiplicity (P defaultPos)
-- Nothing
multiplicity :: Kind -> Maybe Multiplicity
multiplicity P = Nothing
multiplicity (Kind _ m) = Just m

-- | Calculates the least upper bound of two kinds.
leastUpperBound :: Kind -> Kind -> Kind
leastUpperBound P _ = P
leastUpperBound _ P = P
leastUpperBound (Kind b m) (Kind b' m') = Kind (max b b') (max m m')

-- | > Bind _ v k a               ~ ∀(v:k). a
--   >                            ~ \[v:k] -> a
data Bind stage a = Bind Pos !(TypeVar stage) !Kind a
  deriving (Lift)

instance HasPos (Bind x a) where
  pos (Bind p _ _ _) = p
