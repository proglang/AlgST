{-# LANGUAGE CPP #-}

-- | Exports the @Generically@ type. With @base >= 4.17.0.0@ this will
-- re-export @GHC.Generics.Generically@.
module AlgST.Util.Generically
  ( Generically (..),
    Generic,
    Rep,
  )
where

import GHC.Generics (Generic, Rep)

#if MIN_VERSION_base(4, 17, 0)

import GHC.Generics (Generically(..))

#else

newtype Generically a = Generically a

#endif
