{-# LANGUAGE DeriveLift #-}
{- |
Module      :  Syntax.Base
Description :  The Base module.
Copyright   :  (c) Bernardo Almeida, LASIGE, Faculty of Sciences, University of Lisbon
                   Andreia Mordido, LASIGE, Faculty of Sciences, University of Lisbon
                   Vasco Vasconcelos, LASIGE, Faculty of Sciences, University of Lisbon
                   Janek Spaderna

This module defines the basic structures (classes and datatypes) such as Positions and
Multiplicity, that will be used the remaining Compiler.
-}

module Syntax.Base
( Variable(..)
, Pos(..) 
, Position(..)
, Multiplicity(..)
, defaultPos
, negPos
) where

import Data.Void
import Language.Haskell.TH.Syntax (Lift)

-- Position

data Pos = Pos Int Int
  deriving (Eq, Ord, Lift)

class Position t where
  pos :: t -> Pos  

instance Position Pos where
  pos = id

instance Position Void where
  pos = absurd

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
