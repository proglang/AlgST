{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
module Main (main) where

import Control.Applicative
import Control.Monad
import Control.Monad.State (evalState)
import Data.Char
import Gauge
import Options.Applicative qualified as O

import Bisimulation.Bisimulation
import Elaboration.ResolveDuality qualified as Dual
import Parse.Read ()
import Syntax.Kind
import Syntax.Type
import Util.FreestState (FreestState, initialState)
import Validation.Kinding (synthetise) 
import Validation.Rename

data Options = Options
  { optInput :: FilePath
  , optOutput :: Maybe FilePath
  }

optionsParser :: O.Parser Options
optionsParser = do
  outputPath <- optional . O.strOption . mconcat $
    [ O.short 'o'
    , O.long "output"
    , O.help "CSV output file"
    ]
  inputPath <- O.strArgument . mconcat $
    [ O.metavar "INPUT"
    , O.help "input .fst file"
    ]
  pure Options
    { optInput = inputPath
    , optOutput = outputPath
    }

optionsInfo :: O.ParserInfo Options
optionsInfo = O.info (optionsParser <**> O.helper) . mconcat $
  [ O.fullDesc
  , O.header "FreeST Bisimulation Benchmarker"
  ]

main :: IO ()
main = do
  opts <- O.execParser optionsInfo

  -- Read input file.
  inputLines <- readFromFile (optInput opts)
  let types :: [(Type, Type)]
      types = [ (read t, read u) | (t, u) <- splitPairs inputLines ]
      benches = zipWith mkBenchmark [1..] types

  -- Prepare the benchmark configuration.
  outConfig <- case optOutput opts of
    Nothing -> do
      pure defaultConfig
    Just fp -> do
      -- Truncate output file. Gauge only appends data which is wrong.
      writeFile fp ""
      pure defaultConfig { csvFile = Just fp }
  let config = outConfig
        { -- Do a minimum of 6 iterations (`minSamples` is an index into a
          -- sequence).
          minSamples = Just 3
        , -- Increase time limit (= run at least for N sec.) to account for
          -- reduced min samples.
          timeLimit = Just 10
        }
  -- Run the benchmarks.
  runMode DefaultMode config [] benches

mkBenchmark :: Int -> (Type, Type) -> Benchmark
mkBenchmark i (t, u) = bench (show i ++ " [FreeST]") $
  whnf (uncurry benchmarkAction) (t, u)

benchmarkAction :: Type -> Type -> Bool
benchmarkAction t u = do
  let tRes = runFreestBench (Dual.resolve t)
  let uRes = runFreestBench (Dual.resolve u)
  let [t', u'] = renameTypes [tRes, uRes]
  bisimilarNoAlpha t' u'

splitPairs :: [a] -> [(a,a)]
splitPairs []       = []
splitPairs [_]      = error "unpaired element"
splitPairs (x:y:as) = (x,y) : splitPairs as

readFromFile :: FilePath -> IO [String]
readFromFile filename = do
  str <- if filename == "-" then getContents else readFile filename
  return
    $ filter (not . isComment)
    $ filter (not . null)
    $ map (dropWhile isSpace)
    $ lines str
  where
    isComment ('-' : '-' : _) = True
    isComment _               = False

_wellFormed :: KindEnv -> Type -> FreestState ()
_wellFormed kEnv = void . synthetise kEnv

runFreestBench :: FreestState a -> a
runFreestBench m = evalState m initialState
