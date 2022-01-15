{-# LANGUAGE NumericUnderscores #-}

module Test.Golden
  ( -- * Golden tests
    goldenTests,
    plainErrors,
    swap,

    -- * Test trees derived from external files
    withTestInputs,

    -- * Exception handling
    protectIO,
    displayException,
  )
where

import Control.Exception
import Control.Monad
import Data.Foldable
import qualified Data.List as List
import Data.Maybe
import AlgST.Util.Error
import System.Directory
import System.FilePath
import Data.CallStack
import qualified Test.Hspec as Hspec
import Test.Hspec.Core.Spec hiding (Node, Tree)
import Test.Hspec.Core.Util
import System.Timeout

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

fileSpec :: HasCallStack => (String -> Either String String) -> FilePath -> Spec
fileSpec run fp = specify (takeFileName fp) do
  -- Files with a name starting with x- are skipped.
  when (take 2 (takeFileName fp) == "x-") do
    pending

  -- Ensures there is a final newline.
  let normalize = unlines . lines

  src <- readFile fp
  -- Give the action 2s to complete.
  mactual <- timeout 2_000_000 $
    case run src of
      Left err -> expectationFailure ("unexpected result:\n" ++ err)
      Right actual -> normalize actual <$ writeFile (fp <.> "actual") actual
  actual <- failNothing "Test timed out." mactual

  let fpExpected = fp <.> "expected"
  hasExpectation <- doesFileExist fpExpected
  when (not hasExpectation) do
    pendingWith $ "Expected output file " ++ fpExpected ++ " does not exist."

  expectation <- normalize <$> readFile fpExpected
  actual `Hspec.shouldBe` expectation

plainErrors :: [PosError] -> String
plainErrors = show

-- | Utilty function mostly used when defining negative
-- tests.
swap :: Either a b -> Either b a
swap = either Right Left

expectationFailure :: HasCallStack => String -> IO a
expectationFailure s = Hspec.expectationFailure s >> mzero

failNothing :: HasCallStack => String -> Maybe a -> IO a
failNothing s = maybe (expectationFailure s) pure
