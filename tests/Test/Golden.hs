{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE TypeApplications #-}

module Test.Golden
  ( withTestInputs,
    goldenTests,
    goldenTestsH,
  )
where

import AlgST.Util.Error
import Control.Exception
import Control.Monad
import Data.CallStack
import Data.Foldable
import Data.List qualified as List
import Data.Maybe
import GHC.Stack
import System.Directory
import System.FilePath
import System.IO
import System.IO.Error
import System.Timeout
import Test

withTestInputs :: HasCallStack => FilePath -> (FilePath -> SpecWith a) -> SpecWith a
withTestInputs dir run = do
  entries <- runIO $ try @IOError $ listDirectory dir

  let grabSources = filter ((".algst" ==) . takeExtension)
      splitSkips = List.partition (isJust . List.stripPrefix "x-")

  case splitSkips . List.sort . grabSources <$> entries of
    Left err -> specify dir \_ -> do
      pendingWith $ displayException err
    Right ([], []) -> specify dir \_ -> do
      pendingWith "no tests defined"
    Right (skipped, evaled) -> parallel do
      for_ evaled \name ->
        run (dir </> name)
      for_ skipped \name ->
        specify name (const pending)

-- | @goldenTests dir spec@ discovers tests (files with extension @.algst@) in
-- the the directory @dir@.
--
-- When a test is run @spec@ is evaluated with the contents of that file. The
-- result will be written to @file <.> ".actual"@ and compared witht the
-- contents of @file <.> ".expected"@.
goldenTests :: (HasCallStack, GoldenOutput a) => FilePath -> (String -> Assertion a) -> Spec
goldenTests dir f = withFrozenCallStack $ goldenTestsH dir \h input ->
  hPutStr h . renderGoldenOutput =<< f input

-- | Like 'goldenTests' but the function is passed a 'Handle'. The test should
-- write the results to the handle.
goldenTestsH :: HasCallStack => FilePath -> (Handle -> String -> Assertion ()) -> Spec
goldenTestsH dir = withFrozenCallStack $ withTestInputs dir . fileSpec

class GoldenOutput a where
  renderGoldenOutput :: a -> String

instance GoldenOutput String where
  renderGoldenOutput = id

instance GoldenOutput Diagnostic where
  renderGoldenOutput = show

instance Foldable f => GoldenOutput (f Diagnostic) where
  renderGoldenOutput = plainErrors

fileSpec :: HasCallStack => (Handle -> String -> Assertion ()) -> FilePath -> Spec
fileSpec example fp = specify (takeFileName fp) do
  -- Ensures there is a final newline.
  let normalize = unlines . lines
  -- Read the source code.
  src <- readFile fp
  -- Give the action 2s to complete.
  let fpActual = fp <.> "actual"
  let runWithTimeout =
        failNothing "Test timed out." =<< timeout 2_000_000 do
          withFile fpActual WriteMode \h ->
            evaluate =<< example h src
  -- If an error occurs during evaluation of `example` we remove any previous
  -- ".actual" files. Use `tryIOError` to ignore any IO errors in this cleanup
  -- code.
  runWithTimeout `onException` tryIOError (removeFile fpActual)
  -- Check that the ".expected" file exists.
  let fpExpected = fp <.> "expected"
  hasExpectation <- doesFileExist fpExpected
  -- Issue a `pending` message if we have no expectation.
  when (not hasExpectation) do
    pendingWith $ "Expected output file " ++ fpExpected ++ " does not exist."
  -- Read the expectation and actual result.
  actual <- readFile fpActual
  expectation <- readFile fpExpected
  -- Check the result.
  normalize actual `shouldBe` normalize expectation
