{-# LANGUAGE NumericUnderscores #-}

module Test.Golden
  ( -- * Golden tests
    goldenTests,
    goldenTestsM,
    plainErrors,
    swap,

    -- * Test trees derived from external files
    withTestInputs,

    -- * Exception handling
    protectIO,
    displayException,
  )
where

import AlgST.Util.Error
import Control.Category ((>>>))
import Control.DeepSeq
import Control.Exception
import Control.Monad
import Data.CallStack
import Data.Foldable
import Data.List qualified as List
import Data.Maybe
import System.Directory
import System.FilePath
import System.Timeout
import Test.Hspec qualified as Hspec
import Test.Hspec.Core.Spec hiding (Node, Tree)
import Test.Hspec.Core.Util

withTestInputs :: HasCallStack => FilePath -> (FilePath -> Spec) -> Spec
withTestInputs dir run = do
  entries <- protectIO $ listDirectory dir

  let grabSources = filter ((".algst" ==) . takeExtension)
      splitSkips = List.partition (isJust . List.stripPrefix "x-")

  case splitSkips . List.sort . grabSources <$> entries of
    Left err -> specify dir do
      pendingWith $ displayException err
    Right ([], []) -> specify dir do
      pendingWith "no tests defined"
    Right (skipped, evaled) -> parallel do
      for_ evaled \name ->
        run (dir </> name)
      for_ skipped \name ->
        specify name pending

-- | Like @'runIO' . 'try'@ but uses 'safeTry' under the hood which ignores
-- asynchronous exceptions.
protectIO :: IO r -> SpecM a (Either SomeException r)
protectIO = runIO . safeTry

-- | @goldenTests dir spec@ discovers tests (files with extension @.algst@) in
-- the the directory @dir@.
--
-- When a test is run @spec@ is evaluated with the contents of that file. A
-- 'Left' result indicates a fatal error, while a 'Right' will be compared with
-- the contents of the corresponding @.expected@ file.
goldenTests :: HasCallStack => FilePath -> (String -> Either String String) -> Spec
goldenTests dir = withTestInputs dir . fileSpec

goldenTestsM :: HasCallStack => FilePath -> (String -> IO String) -> Spec
goldenTestsM dir = withTestInputs dir . fileSpecM

fileSpec :: HasCallStack => (String -> Either String String) -> FilePath -> Spec
fileSpec f = fileSpecM $ f >>> either expectationFailure pure

fileSpecM :: HasCallStack => (String -> IO String) -> FilePath -> Spec
fileSpecM run fp = specify (takeFileName fp) do
  -- Files with a name starting with "x-" are skipped.
  when (take 2 (takeFileName fp) == "x-") do
    pending

  -- Ensures there is a final newline.
  let normalize = unlines . lines

  -- Read the source code.
  src <- readFile fp

  -- Give the action 2s to complete.
  actual <-
    failNothing "Test timed out." =<< timeout 2_000_000 do
      s <- run src
      evaluate $ force s

  -- Write the result to the ".actual" file.
  writeFile (fp <.> "actual") actual

  -- Read the expectation.
  let fpExpected = fp <.> "expected"
  hasExpectation <- doesFileExist fpExpected
  when (not hasExpectation) do
    pendingWith $ "Expected output file " ++ fpExpected ++ " does not exist."
  expectation <- readFile fpExpected

  -- Check the result.
  normalize actual `Hspec.shouldBe` normalize expectation

plainErrors :: Foldable f => f Diagnostic -> String
plainErrors = show . toList

-- | Utilty function mostly used when defining negative
-- tests.
swap :: Either a b -> Either b a
swap = either Right Left

expectationFailure :: HasCallStack => String -> IO a
expectationFailure s = Hspec.expectationFailure s >> mzero

failNothing :: HasCallStack => String -> Maybe a -> IO a
failNothing s = maybe (expectationFailure s) pure
