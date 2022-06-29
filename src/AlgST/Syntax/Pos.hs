{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE PatternSynonyms #-}

module AlgST.Syntax.Pos
  ( -- * Positions
    Pos (ZeroPos, ..),

    -- * Located things
    HasPos (..),
    Located (..),
    (@-),
    unL,
    foldL,
    uncurryL,
    onUnL,

    -- * Algorithms on located things
    earlier,
  )
where

import Data.Void
import Language.Haskell.TH.Syntax (Lift)

data Pos = Pos !Int !Int
  deriving stock (Eq, Ord, Lift)

instance Show Pos where
  showsPrec _ = \case
    ZeroPos -> showString "«unknown location»"
    p -> shows (posLn p) . showChar ':' . shows (posCol p)

posLn :: Pos -> Int
posLn (Pos l _) = l

posCol :: Pos -> Int
posCol (Pos _ c) = c

class HasPos t where
  pos :: t -> Pos

instance HasPos Pos where
  pos = id

instance HasPos Void where
  pos = absurd

instance HasPos (Located a) where
  pos (p :@ _) = p

instance (HasPos a, HasPos b) => HasPos (Either a b) where
  pos = either pos pos

-- | An unknown/unspecified location.
pattern ZeroPos :: Pos
pattern ZeroPos = Pos 0 0

-- | Attaches a position to a value of type @a@.
--
-- Ordering/Equality is not defined for this type to avoid confusion wether the
-- position is considered or not. The function 'onUnL' is provided to
-- simplify comparing and similar functions which do not consider the
-- position.
data Located a = !Pos :@ a
  deriving stock (Show, Lift)
  deriving stock (Functor, Foldable, Traversable)

infix 9 :@, @-

unL :: Located a -> a
unL (_ :@ a) = a

foldL :: (a -> b) -> Located a -> b
foldL f = f . unL

uncurryL :: (Pos -> a -> b) -> Located a -> b
uncurryL f (p :@ a) = f p a

onUnL :: (a -> a -> b) -> Located a -> Located a -> b
onUnL f (_ :@ x) (_ :@ y) = f x y

(@-) :: HasPos p => p -> a -> Located a
p @- a = pos p :@ a

-- | Return the element located earlier. An equal location gives precedence to
-- the first argument.
--
-- 'defaultPos' does not get special treatement and is considered the earliest
-- valid location. (If required this behaviour could be changed to give
-- precedence to properly located arguments first.)
earlier :: HasPos a => a -> a -> a
earlier x y
  | pos x <= pos y = x
  | otherwise = y
