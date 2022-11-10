module Main (main) where

import Control.Monad.Reader
import Data.Foldable
import System.Directory
import System.Environment
import System.Exit (exitFailure)
import System.FilePath
import System.Process.Typed

newtype Opts = Opts
  { optsVerbose :: Bool
  }

type M = ReaderT Opts IO

main :: IO ()
main = do
  opts <- readOpts

  let base = "./examples"
  examples <- fmap (base </>) <$> listDirectory base

  when (optsVerbose opts) do
    for_ examples putStrLn

  results <- runReaderT (traverse checkPath examples) opts
  let nall = length results
      ngood = length $ filter id results

  putStrLn . unwords $
    [ show nall,
      plural nall "example," "examples,",
      show ngood,
      "good,",
      show (nall - ngood),
      "failed"
    ]

  when (nall /= ngood) do
    exitFailure

plural :: Int -> a -> a -> a
plural 1 one _ = one
plural _ _ n = n

readOpts :: IO Opts
readOpts =
  getArgs >>= \case
    [] -> pure Opts {optsVerbose = False}
    [arg] | arg == "-v" || arg == "--verbose" -> pure Opts {optsVerbose = True}
    _ -> do
      name <- getProgName
      putStrLn $ "usage: " ++ name ++ " [-v|--verbose]"
      exitFailure

checkPath :: FilePath -> M Bool
checkPath fp
  | takeExtension fp == ".algst" = checkFile fp
  | otherwise = checkModule fp

checkFile :: FilePath -> M Bool
checkFile fp = run desc args
  where
    desc = "Checking ‘" ++ fp ++ "’"
    args = [fp]

checkModule :: FilePath -> M Bool
checkModule dir = run desc args
  where
    desc = "Checking ‘" ++ dir ++ "’"
    args = ["--search-dir", dir, "--find-main"]

run :: String -> [String] -> M Bool
run desc args = do
  opts <- ask
  lift . putStrLn $
    if optsVerbose opts
      then desc
      else "algst " ++ unwords args

  exit <- runProcess $ proc "algst" args
  when (optsVerbose opts || exit /= ExitSuccess) do
    lift $ putStrLn $ "exited with " ++ show exit
  lift $ putChar '\n'

  pure $ exit == ExitSuccess
