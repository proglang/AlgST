{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module AlgST.Syntax.Pos
  ( -- * Positions
    Pos (ZeroPos, ..),

    -- * Located things
    HasPos (..),
    GHasPos,
    Generically (..),
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

import AlgST.Util.Generically
import Data.Void
import GHC.Generics
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

instance (Generic a, GHasPos (Rep a)) => HasPos (Generically a) where
  pos (Generically a) = gpos (from a)

-- | Extracts the @Pos@ from the leftmost component of each constructor.
class GHasPos f where
  gpos :: f a -> Pos

instance (GHasPos f, GHasPos g) => GHasPos (f :+: g) where
  gpos (L1 f) = gpos f
  gpos (R1 g) = gpos g

instance GHasPos f => GHasPos (f :*: g) where
  gpos (f :*: _) = gpos f

instance GHasPos f => GHasPos (M1 i c f) where
  gpos (M1 f) = gpos f

instance HasPos c => GHasPos (K1 i c) where
  gpos (K1 c) = pos c
