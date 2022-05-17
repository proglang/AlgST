{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}

module AlgST.Rename.Fresh
  ( Fresh (..),
    runFresh,
    etaFresh,
    currentModule,
    freshResolved,
    freshResolvedParams,
    freshResolved',
  )
where

import AlgST.Syntax.Decl (Params)
import AlgST.Syntax.Name
import Control.Monad.Eta
import Control.Monad.Reader
import Control.Monad.State.Strict
import Data.Bitraversable

newtype Fresh a = Fresh {unFresh :: ReaderT ModuleName (State ResolvedId) a}
  deriving newtype (Functor, Applicative, Monad, MonadFix)

{- ORMOLU_DISABLE -}
-- TODO: Change these `Resolved` and `NameR` respectively and unfold the type
-- aliases.
type FStage = Written
type FName = NameW
{- ORMOLU_ENABLE -}

runFresh :: ModuleName -> Fresh a -> a
runFresh m (Fresh a) = evalState (runReaderT a m) firstResolvedId

currentModule :: Fresh ModuleName
currentModule = Fresh ask

freshResolved :: Name stage scope -> Fresh (FName scope)
freshResolved n = do
  _mod <- currentModule
  Fresh $ state \ !nextId ->
    -- TODO: Return a resolved name.
    -- (ResolvedName (nameWritten n) mod nextId, nextResolvedId nextId)
    (nameWritten n, nextResolvedId nextId)

freshResolved' :: Name stage scope -> Fresh (NameR scope)
freshResolved' n = do
  mod <- currentModule
  Fresh $ state \ !nextId ->
    (ResolvedName (nameWritten n) mod nextId, nextResolvedId nextId)

freshResolvedParams :: Params stage -> Fresh (Params FStage)
freshResolvedParams = traverse (bitraverse (traverse freshResolved) pure)

etaFresh :: Fresh a -> Fresh a
etaFresh = Fresh . etaReaderT . mapReaderT etaStateT . unFresh
{-# INLINE etaFresh #-}
