{-# LANGUAGE DeriveLift #-}
{- |
Module      :  Syntax.TypeVariable
Description :  The type variables
Copyright   :  (c) Bernardo Almeida, LASIGE, Faculty of Sciences, University of Lisbon
                   Andreia Mordido, LASIGE, Faculty of Sciences, University of Lisbon
                   Vasco Vasconcelos, LASIGE, Faculty of Sciences, University of Lisbon
-}

module Syntax.TypeVariable
( TypeVar
) where

import Syntax.Base
import Language.Haskell.TH.Syntax (Lift)

data TypeVar = TypeVar Pos String
  deriving (Lift)

instance Variable TypeVar where
  mkVar = TypeVar
  mkNewVar next (TypeVar p str) = TypeVar p (show next ++ '#' : str)
  intern (TypeVar _ x) = x

instance Eq TypeVar where
  (TypeVar _ x) == (TypeVar _ y) = x == y
  
instance Ord TypeVar where
  (TypeVar _ x) <= (TypeVar _ y) = x <= y

instance Position TypeVar where
  pos (TypeVar p _) = p
