{-# LANGUAGE FlexibleInstances #-}

module AlgST.Util.Lenses where

import Control.Monad
import qualified Language.Haskell.TH as TH
import qualified Lens.Family2.TH as Lens

class LensResult a where
  makeLenses :: a

-- | Makes lenses for all fields by appending a @L@ at the end.
instance LensResult (TH.Name -> TH.DecsQ) where
  makeLenses = Lens.makeLensesBy (Just . (++ "L"))

-- | Makes lenses for the given fields by appending a @L@ at the end.
instance LensResult ([TH.Name] -> TH.Name -> TH.DecsQ) where
  makeLenses names = Lens.makeLensesBy \n -> do
    guard $ n `elem` fmap TH.nameBase names
    pure $ n ++ "L"
