{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Test
  ( module Test.Hspec,
    module Export,

    -- * Formatting errors
    plainErrors,

    -- * Assertions
    Assertion,
    expectationFailure,
    failNothing,
    AssertMsg (..),
    Assertable (..),
    (@?),
    (@!?),
    Lines (..),
    Words (..),

    -- ** Handling Diagnostics
    DiagnosticException (..),
    shouldNotError,
    expectDiagnostics,
    expectDiagnostics_,

    -- * Operation shortcuts

    -- ** Parsing
    shouldParse,

    -- ** Renaming
    withRenameContext,
    withRenameContext',

    -- ** Type Checking
    withTcContext,
    withTcContext',
  )
where

import AlgST.Builtins
import AlgST.Parse.Parser
import AlgST.Rename
import AlgST.Syntax.Module
import AlgST.Syntax.Name
import AlgST.Typing
import AlgST.Util.Error
import Control.Category as Export ((<<<), (>>>))
import Control.Exception
import Control.Monad
import Control.Monad as Export ((<=<), (>=>))
import Data.Bifunctor
import Data.Foldable
import Data.List.NonEmpty (NonEmpty (..))
import Data.Typeable
import GHC.Stack
import Test.Hspec hiding (expectationFailure)
import Test.Hspec qualified as Hspec

-- | Type alias for documentation purposes.
type Assertion = IO

plainErrors :: Foldable f => f Diagnostic -> String
plainErrors = show . toList

expectationFailure :: HasCallStack => String -> Assertion a
expectationFailure = Hspec.expectationFailure >=> const mzero

failNothing :: HasCallStack => String -> Maybe a -> Assertion a
failNothing s = maybe (expectationFailure s) pure

data DiagnosticException = DiagnosticException CallStack Errors

instance Show DiagnosticException where
  show (DiagnosticException stack diags) = plainErrors diags ++ prettyStack
    where
      prettyStack = case prettyCallStack stack of
        "" -> ""
        str -> '\n' : '\n' : str

instance Exception DiagnosticException

newtype Lines a = Lines [a]

newtype Words a = Words [a]

class AssertMsg a bad where
  mkAssertMsg :: a -> bad -> String

instance AssertMsg String bad where
  mkAssertMsg = const

instance AssertMsg (bad -> String) bad where
  mkAssertMsg = id

class Assertable a bad good | a -> bad good where
  runAssertable :: a -> Assertion (Either bad good)

instance Assertable Bool () () where
  runAssertable True = pure $ Right ()
  runAssertable False = pure $ Left ()

instance Assertable (Maybe a) () a where
  runAssertable Nothing = pure $ Left ()
  runAssertable (Just a) = pure $ Right a

instance Assertable (Either a b) a b where
  runAssertable = pure

instance Assertable a bad good => Assertable (IO a) bad good where
  runAssertable = (>>= runAssertable)

newtype Invert a = Invert a

instance Assertable a bad good => Assertable (Invert a) good bad where
  runAssertable (Invert a) = either Right Left <$> runAssertable a

infix 1 @?, @!?

(@?) :: (HasCallStack, Assertable a bad good, AssertMsg msg bad) => a -> msg -> Assertion good
(@?) a msg = withFrozenCallStack do
  runAssertable a >>= \case
    Left bad -> expectationFailure (mkAssertMsg msg bad)
    Right good -> pure good

(@!?) :: (HasCallStack, Assertable a bad good, AssertMsg msg good) => a -> msg -> Assertion bad
(@!?) a msg = withFrozenCallStack $ Invert a @? msg

expectDiagnostics :: (HasCallStack, Show a, Typeable a) => Assertion a -> Assertion Errors
expectDiagnostics = withFrozenCallStack do
  try >=> \case
    Left (DiagnosticException _ diags) -> pure diags
    Right a
      | Just () <- cast a -> expectationFailure msg
      | Just s <- cast a -> expectationFailure (msg ++ ": " ++ s)
      | otherwise -> expectationFailure (msg ++ ": " ++ show a)
      where
        msg = "expectDiagnostics: nested computation finished successfully"

expectDiagnostics_ :: HasCallStack => Assertion a -> Assertion Errors
expectDiagnostics_ = expectDiagnostics . void

shouldNotError :: (HasCallStack, Foldable f) => Either (f Diagnostic) a -> Assertion a
shouldNotError = withFrozenCallStack do
  first toList >>> \case
    Left [] -> expectationFailure "shouldNotError: received a `Left` but without any errors"
    Left (e : es) -> throwIO $ DiagnosticException callStack (e :| es)
    Right a -> pure a

shouldParse :: HasCallStack => Parser a -> String -> Assertion a
shouldParse p = withFrozenCallStack $ shouldNotError . runParser p

withRenameContext :: HasCallStack => RnM a -> Assertion a
withRenameContext = withFrozenCallStack $ withRenameContext' builtinsEnv

withRenameContext' :: HasCallStack => RenameEnv -> RnM a -> Assertion a
withRenameContext' env body = withFrozenCallStack $ shouldNotError do
  let (_, getExtra) = renameModuleExtra (ModuleName "WithRenameContext") emptyModule
  RenameExtra f <- getExtra env
  f $ const body

withTcContext ::
  (forall env st. (HasKiEnv env, HasKiSt st) => RunTyM env st -> TcM env st a) -> RnM a
withTcContext = withFrozenCallStack $ withTcContext' builtinsModuleCtxt

withTcContext' ::
  CheckContext ->
  (forall env st. (HasKiEnv env, HasKiSt st) => RunTyM env st -> TcM env st a) ->
  RnM a
withTcContext' ctx body = withFrozenCallStack do
  checkResultAsRnM $ checkWithModule ctx emptyModule \runTyM _ -> body runTyM
