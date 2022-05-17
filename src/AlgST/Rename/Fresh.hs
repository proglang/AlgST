{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}

module AlgST.Rename.Fresh
  ( Fresh,
    FreshT (..),
    runFresh,
    runFreshT,
    etaFresh,
    currentModule,
    freshResolved,
    freshResolvedParams,
  )
where

import AlgST.Syntax.Decl (Params)
import AlgST.Syntax.Name
import Control.Monad.Eta
import Control.Monad.Reader
import Control.Monad.State.Strict
import Data.Bitraversable
import Data.Functor.Identity

newtype FreshT m a = Fresh {unFresh :: ReaderT ModuleName (StateT ResolvedId m) a}
  deriving newtype (Functor, Applicative, Monad, MonadFix)

type Fresh = FreshT Identity

instance MonadTrans FreshT where
  lift = Fresh . lift . lift

runFreshT :: Monad m => ModuleName -> FreshT m a -> m a
runFreshT m (Fresh a) = evalStateT (runReaderT a m) firstResolvedId

runFresh :: ModuleName -> Fresh a -> a
runFresh m = runIdentity . runFreshT m

currentModule :: Monad m => FreshT m ModuleName
currentModule = Fresh ask

freshResolved :: Monad m => Name stage scope -> FreshT m (NameR scope)
freshResolved n = do
  mod <- currentModule
  Fresh $ state \ !nextId ->
    (ResolvedName (nameWritten n) mod nextId, nextResolvedId nextId)

freshResolvedParams :: Monad m => Params stage -> FreshT m (Params Resolved)
freshResolvedParams = traverse (bitraverse (traverse freshResolved) pure)

etaFresh :: Fresh a -> Fresh a
etaFresh = Fresh . etaReaderT . mapReaderT etaStateT . unFresh
{-# INLINE etaFresh #-}
