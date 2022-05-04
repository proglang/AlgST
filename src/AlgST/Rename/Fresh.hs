{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE RankNTypes #-}

module AlgST.Rename.Fresh
  ( Fresh,
    runFresh,
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

newtype Fresh a = Fresh {unFresh :: ReaderT Module (State ResolvedId) a}
  deriving newtype (Functor, Applicative, Monad, MonadFix)

{- ORMOLU_DISABLE -}
-- TODO: Change these `Resolved` and `NameR` respectively and unfold the type
-- aliases.
type FStage = Written
type FName = NameW
{- ORMOLU_ENABLE -}

runFresh :: Module -> Fresh a -> a
runFresh m (Fresh a) = evalState (runReaderT a m) firstResolvedId

currentModule :: Fresh Module
currentModule = Fresh ask

freshResolved :: Name stage scope -> Fresh (FName scope)
freshResolved n = do
  _mod <- currentModule
  Fresh $ state \ !nextId ->
    -- TODO: Return a resolved name.
    -- (ResolvedName (nameWritten n) mod nextId, nextResolvedId nextId)
    (nameWritten n, nextResolvedId nextId)

freshResolvedParams :: Params stage -> Fresh (Params FStage)
freshResolvedParams = traverse (bitraverse (traverse freshResolved) pure)

etaFresh :: Fresh a -> Fresh a
etaFresh = Fresh . etaReaderT . mapReaderT etaStateT . unFresh
{-# INLINE etaFresh #-}
