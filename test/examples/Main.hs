module Main (main) where

import Control.Monad.Reader
import Data.Foldable
import Data.Function
import Data.List qualified as List
import Data.Semialign
import Data.These
import Paths_AlgST
import System.Directory
import System.Environment
import System.Exit (exitFailure)
import System.FilePath
import System.Process.Typed

data Opts = Opts
  { optsVerbose :: !Bool,
    optsOnly :: [FilePath],
    optsDir :: FilePath
  }

type M = ReaderT Opts IO

main :: IO ()
main = do
  opts <- readOpts

  let doFilter flt fp = and $ alignWith go (splitRev flt) (splitRev fp)
        where
          splitRev = reverse . splitDirectories . normalise
          go (These flt' fp') =
            flt' == fp'
              || (not (hasExtension flt') && flt' == dropExtensions fp')
          go (This _) = False -- filter has more components
          go (That _) = True -- filter is shorter
  let testFilter fp
        | null (optsOnly opts) = True
        | otherwise = any (doFilter fp) (optsOnly opts)

  dataDir <- getDataDir
  allExamples <- listDirectory (dataDir </> "examples")
  let prefixed = ("examples" </>) <$> allExamples
  let filtered = List.sort $ filter testFilter prefixed
  let selected = (dataDir </>) <$> filtered

  when (optsVerbose opts) do
    for_ filtered putStrLn

  let runOpts = opts {optsDir = dataDir}
  results <- runReaderT (traverse checkPath selected) runOpts
  let nall = length allExamples
      nrun = length results
      ngood = length $ filter id results

  putStrLn . unwords $
    [ show nall,
      plural nall "example," "examples,",
      show ngood,
      "good,",
      show (nrun - ngood),
      "failed,",
      show (nall - nrun),
      "skipped"
    ]

  when (nall /= ngood) do
    exitFailure

plural :: Int -> a -> a -> a
plural 1 one _ = one
plural _ _ n = n

readOpts :: IO Opts
readOpts =
  getArgs >>= \case
    [] -> pure def
    a : as
      | a == "-h" || a == "--help" -> usage
      | a == "-v" || a == "--verbose" -> pure def {optsVerbose = True, optsOnly = as}
      | otherwise -> pure def {optsVerbose = False, optsOnly = a : as}
  where
    def = Opts {optsVerbose = False, optsOnly = [], optsDir = "."}
    usage = do
      name <- getProgName
      putStrLn $ "usage: " ++ name ++ " [-v|--verbose] [examples...]"
      exitFailure

checkPath :: FilePath -> M Bool
checkPath fp
  | takeExtension fp == ".algst" = checkFile fp
  | otherwise = checkModule fp

checkFile :: FilePath -> M Bool
checkFile fp = run desc args
  where
    desc = "Checking ‘" ++ takeFileName fp ++ "’"
    args = [fp]

checkModule :: FilePath -> M Bool
checkModule dir = run desc args
  where
    desc = "Checking ‘" ++ takeFileName dir ++ "’"
    args = ["--search-dir", dir, "--find-main"]

run :: String -> [String] -> M Bool
run desc args = do
  opts <- ask
  lift . putStrLn $
    if optsVerbose opts
      then "algst " ++ unwords args
      else desc

  let process =
        proc "algst" args
          & setWorkingDir (optsDir opts)
  exit <- runProcess process
  when (optsVerbose opts || exit /= ExitSuccess) do
    lift $ putStrLn $ "exited with " ++ show exit
  lift $ putChar '\n'

  pure $ exit == ExitSuccess
