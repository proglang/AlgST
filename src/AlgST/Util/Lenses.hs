{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}

module AlgST.Util.Lenses where

import Control.Monad
import Data.Coerce
import Data.HashMap.Strict qualified as HM
import Data.Hashable (Hashable)
import Language.Haskell.TH qualified as TH
import Lens.Family2
import Lens.Family2.TH qualified as Lens
import Lens.Family2.Unchecked qualified as L

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

coerced :: forall b a. Coercible a b => Lens' a b
coerced f = fmap coerce . f . coerce
{-# INLINE coerced #-}

coercing :: (Coercible s a, Coercible t b) => Adapter s t a b
coercing = L.adapter coerce coerce
{-# INLINE coercing #-}

hashAt :: (Eq k, Hashable k) => k -> Lens' (HM.HashMap k v) (Maybe v)
hashAt k f = HM.alterF f k
