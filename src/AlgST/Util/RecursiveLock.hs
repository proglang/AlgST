{-# LANGUAGE RankNTypes #-}

module AlgST.Util.RecursiveLock
  ( RecursiveLock,
    newRecursiveLockIO,
    withRecursiveLock,
  )
where

import Control.Applicative
import Control.Concurrent
import Control.Concurrent.STM
import Control.Exception
import Control.Monad
import Data.Foldable
import Data.Maybe

data RecursiveLock a = RecursiveLock a !(TVar (Maybe ThreadId)) !(TQueue ThreadId)

newRecursiveLockIO :: a -> IO (RecursiveLock a)
newRecursiveLockIO a = RecursiveLock a <$> newTVarIO Nothing <*> newTQueueIO

withRecursiveLock :: RecursiveLock a -> (a -> IO b) -> IO b
withRecursiveLock lock@(RecursiveLock a _ _) inner =
  uninterruptibleMask \restore -> do
    releaseOp <- acquire restore lock
    restore (inner a) `finally` atomically releaseOp

data State = Holding | Locked | Waiting

acquire :: (forall x. IO x -> IO x) -> RecursiveLock a -> IO (STM ())
acquire restore lock@(RecursiveLock _ current nextQ) = do
  tid <- myThreadId
  let checkHasLock = do
        other <- readTVar current
        check $ Just tid == other
        pure Holding
  let lockFirst = do
        -- No thread holding the lock implies no waiting threads either. The
        -- current thread can acquire the lock.
        other <- readTVar current
        check $ isNothing other
        writeTVar current $ Just tid
        pure Locked
  let registerWait = do
        writeTQueue nextQ tid
        pure Waiting
  status <- atomically $ lockFirst <|> (checkHasLock <|> registerWait)
  case status of
    -- Thread already holds the lock. Nothing to do, unlock should do nothing
    -- either.
    Holding -> do
      pure $ pure ()

    -- Thread acquired the lock. We have to release the lock afterwards.
    Locked -> do
      pure $ release lock

    -- Lock is held by another thread. Wait until our current thread is allowed
    -- to enter by the release operation of the other thread. We have to
    -- release the lock afterwards.
    --
    -- Waiting on the lock may be canceled, in which case we have to remove the
    -- current thread from the list of interested parties.
    Waiting -> do
      let delist = do
            -- If we have become the lock owners we release the lock.
            -- Otherwise remove `tid` from the queue.
            owner <- readTVar current
            if owner == Just tid
              then release lock
              else unqueue tid nextQ
      void $ restore (atomically checkHasLock) `onException` atomically delist
      pure $ release lock

unqueue :: Eq a => a -> TQueue a -> STM ()
unqueue a q = go []
  where
    go as = do
      mhead <- tryReadTQueue q
      case mhead of
        Just a' | a /= a' -> do
          go (a' : as)
        _ -> do
          traverse_ (unGetTQueue q) mhead
          traverse_ (unGetTQueue q) as

release :: RecursiveLock a -> STM ()
release (RecursiveLock _ current nextQ) = do
  -- This function assumes that the current thread is the rightful owner.
  next <- tryReadTQueue nextQ
  writeTVar current next
