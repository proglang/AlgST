{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingStrategies #-}

-- |
-- Module      :  Syntax.Base
-- Description :  The Base module.
-- Copyright   :  (c) Bernardo Almeida, LASIGE, Faculty of Sciences, University of Lisbon
--                    Andreia Mordido, LASIGE, Faculty of Sciences, University of Lisbon
--                    Vasco Vasconcelos, LASIGE, Faculty of Sciences, University of Lisbon
--                    Janek Spaderna
--
-- This module defines the basic structures (classes and datatypes) such as Positions and
-- Multiplicity, that will be used the remaining Compiler.
module Syntax.Base
  ( Pos (..),
    Located (..),
    (@-),
    unL,
    foldL,
    uncurryL,
    onUnL,
    Position (..),
    Multiplicity (..),
    defaultPos,
    negPos,
  )
where

import Data.Void
import Language.Haskell.TH.Syntax (Lift)

-- Position

data Pos = Pos !Int !Int
  deriving stock (Eq, Ord, Lift)

instance Show Pos where
  show (Pos l c) = show l ++ ":" ++ show c

-- | Attaches a position to a value of type @a@.
--
-- Ordering/Equality is not defined for this type to avoid confusion wether the
-- position is considered or not. The function 'onUnL' is provided to
-- simplify comparing and similar functions which do not consider the
-- position.
data Located a = !Pos :@ a
  deriving stock (Lift)
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

(@-) :: Position p => p -> a -> Located a
p @- a = pos p :@ a

class Position t where
  pos :: t -> Pos

instance Position Pos where
  pos = id

instance Position Void where
  pos = absurd

instance Position (Located a) where
  pos (p :@ _) = p

instance (Position a, Position b) => Position (Either a b) where
  pos = either pos pos

defaultPos :: Pos
defaultPos = Pos 0 0

negPos :: Pos -> Pos
negPos (Pos i j) = Pos (negate i) (negate j)

-- Multiplicity for types and expressions

data Multiplicity = Un | Lin
  deriving (Eq, Lift, Ord)
