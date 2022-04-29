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
  ( Variable (..),
    Pos (..),
    Located (..),
    (@),
    unL,
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

-- | Attaches a position to a value of type @a@.
--
-- Ordering/Equality is not defined for this type to avoid confusion wether the
-- position is considered or not.
data Located a = !Pos :@ a
  deriving stock (Lift)
  deriving stock (Functor, Foldable, Traversable)

unL :: Located a -> a
unL (_ :@ a) = a

(@) :: Position p => p -> a -> Located a
p @ a = pos p :@ a

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

-- Type and program variable

class Position t => Variable t where
  -- The string, internal representation of a variable
  intern :: t -> String

  -- Making a variable from a string, type or program
  mkVar :: Pos -> String -> t

  -- Making a new variable from a given variable. The variable is
  -- unique up to the point where the integer is
  mkNewVar :: Int -> t -> t
