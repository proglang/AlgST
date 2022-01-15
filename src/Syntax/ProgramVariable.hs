{-# LANGUAGE DeriveLift #-}
{- |
Module      :  Syntax.ProgramVariables
Description :  The program variables
Copyright   :  (c) Bernardo Almeida, LASIGE, Faculty of Sciences, University of Lisbon
                   Andreia Mordido, LASIGE, Faculty of Sciences, University of Lisbon
                   Vasco Vasconcelos, LASIGE, Faculty of Sciences, University of Lisbon

The definition of program variables
-}

module Syntax.ProgramVariable
( ProgVar
) where

import Syntax.Base
import Language.Haskell.TH.Syntax (Lift)

-- Note: isomorphic to TypeVariables: Type <-> Prog
data ProgVar = ProgVar Pos String
  deriving (Lift)

instance Variable ProgVar where
  mkVar = ProgVar
  mkNewVar next (ProgVar p id) = ProgVar p (show next ++ '#' : id)
  intern (ProgVar _ x) = x

instance Eq ProgVar where
  (ProgVar _ x) == (ProgVar _ y) = x == y
  
instance Ord ProgVar where
  (ProgVar _ x) <= (ProgVar _ y) = x <= y

instance Position ProgVar where
  pos (ProgVar p _) = p
