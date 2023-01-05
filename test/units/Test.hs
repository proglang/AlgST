{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test
  ( module Test.Hspec,
    module Export,

    -- * Formatting errors
    plainErrors,

    -- * Assertions
    Assertion,
    expectationFailure,
    failNothing,

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

newtype DiagnosticException = DiagnosticException Errors

instance Show DiagnosticException where
  show (DiagnosticException diags) = plainErrors diags

instance Exception DiagnosticException

expectDiagnostics :: (HasCallStack, Show a, Typeable a) => Assertion a -> Assertion Errors
expectDiagnostics =
  try >=> \case
    Left (DiagnosticException diags) -> pure diags
    Right a
      | Just (_ :: ()) <- cast a -> expectationFailure msg
      | Just s <- cast a -> expectationFailure (msg ++ ": " ++ s)
      | otherwise -> expectationFailure (msg ++ ": " ++ show a)
      where
        msg = "expectDiagnostics: nested computation finished successfully"

expectDiagnostics_ :: HasCallStack => Assertion a -> Assertion Errors
expectDiagnostics_ = expectDiagnostics . void

shouldNotError :: (HasCallStack, Foldable f) => Either (f Diagnostic) a -> Assertion a
shouldNotError =
  first toList >>> \case
    Left [] -> expectationFailure "shouldNotError: `Left` but no errors were given"
    Left (e : es) -> throwIO $ DiagnosticException (e :| es)
    Right a -> pure a

shouldParse :: Parser a -> String -> Assertion a
shouldParse p = shouldNotError . runParser p

withRenameContext :: RnM a -> Assertion a
withRenameContext = withRenameContext' builtinsEnv

withRenameContext' :: RenameEnv -> RnM a -> Assertion a
withRenameContext' env body = shouldNotError do
  let (_, getExtra) = renameModuleExtra (ModuleName "WithRenameContext") emptyModule
  RenameExtra f <- getExtra env
  f $ const body

withTcContext ::
  (forall env st. (HasKiEnv env, HasKiSt st) => RunTyM env st -> TcM env st a) -> RnM a
withTcContext = withTcContext' builtinsModuleCtxt

withTcContext' ::
  CheckContext ->
  (forall env st. (HasKiEnv env, HasKiSt st) => RunTyM env st -> TcM env st a) ->
  RnM a
withTcContext' ctx body =
  checkResultAsRnM $ checkWithModule ctx emptyModule \runTyM _ -> body runTyM
