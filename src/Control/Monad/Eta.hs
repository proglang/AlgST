-- | A module for eta-expanding monad stacks. This can improve runtime
-- performance as explained by Joachim Breitner in
-- [Faster Winter 5: Eta-Expanding ReaderT](https://www.joachim-breitner.de/blog/763-Faster_Winter_5__Eta-Expanding_ReaderT).
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Control.Monad.Eta
  ( module Control.Monad.Eta,
    oneShot,
  )
where

import Control.Monad.Trans.Except
import Control.Monad.Trans.Reader
import Control.Monad.Trans.State.Strict
import Control.Monad.Validate.Internal
import GHC.Exts (oneShot)
import Data.Functor.Identity

etaReaderT :: ReaderT r m a -> ReaderT r m a
etaReaderT = ReaderT . oneShot . runReaderT
{-# INLINE etaReaderT #-}

etaStateT :: StateT s m a -> StateT s m a
etaStateT = StateT . oneShot . runStateT
{-# INLINE etaStateT #-}

seqStateT :: Monad m => StateT s m a -> StateT s m a
seqStateT m = StateT \ !s -> do
  (a, !s') <- runStateT m s
  pure (a, s')
{-# INLINE seqStateT #-}

etaValidateT :: forall e m a. ValidateT e m a -> ValidateT e m a
etaValidateT x =
  -- Can't be written in point-free style because of the RankNType in ValidateT.
  ValidateT (etaStateT (getValidateT x))
{-# INLINE etaValidateT #-}

mapValidateT :: (forall x. m x -> n x) -> ValidateT e m a -> ValidateT e n a
mapValidateT f x =
  -- Can't be written in point-free style because of the RankNType in ValidateT.
  ValidateT (mapStateT (mapExceptT f) (getValidateT x))
{-# INLINE mapValidateT #-}

embedValidate :: Applicative m => Validate e a -> ValidateT e m a
embedValidate = mapValidateT (pure . runIdentity)
{-# INLINE embedValidate #-}
