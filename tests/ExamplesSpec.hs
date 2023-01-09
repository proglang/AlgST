module ExamplesSpec where

import Data.Foldable
import Data.Functor
import Data.List qualified as List
import Paths_AlgST
import System.Directory
import System.FilePath
import System.Process.Typed
import Test

spec :: Spec
spec = parallel do
  (examplesDir, allExamples) <- runIO do
    examplesDir <- getDataDir <&> (</> "examples")
    allExamples <- listDirectory examplesDir
    pure (examplesDir, List.sort allExamples)

  -- We might want to throw a `parallel` in here but (at least at the moment)
  -- it does not seem as if the runtime would actually decrease.
  for_ allExamples \example ->
    specify example do
      checkPath (examplesDir </> example)

checkPath :: FilePath -> Expectation
checkPath example
  | takeExtension example == ".algst" = checkFile example
  | otherwise = checkModule example

checkFile :: FilePath -> Expectation
checkFile fp = run [fp]

checkModule :: FilePath -> Expectation
checkModule dir = run ["--search-dir", dir, "--find-main"]

run :: [String] -> Expectation
run args = runProcess_ $ proc "algst" ("--quiet" : args)
