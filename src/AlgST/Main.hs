module AlgST.Main (main) where

import AlgST.CommandLine
import AlgST.Driver (Settings (..))
import AlgST.Driver qualified as Driver
import AlgST.Driver.Output
import AlgST.Interpret qualified as I
import AlgST.Syntax.Expression qualified as E
import AlgST.Syntax.Name
import AlgST.Syntax.Program
import AlgST.Util.Output
import Control.Applicative
import Control.Monad
import Control.Monad.Reader
import Control.Monad.Trans.Maybe
import Data.Foldable
import Data.Function
import Data.List qualified as List
import Data.Map.Strict qualified as Map
import Syntax.Base
import System.Exit
import System.IO

main :: IO ()
main = do
  runOpts <- getOptions
  stderrMode <- maybe (discoverMode stderr) pure (optsOutputMode runOpts)

  let allowAnsi = stderrMode /= Plain
  withOutput allowAnsi stderr \outputHandle -> do
    inputIsTerm <- (sourceIsTerm (optsSource runOpts) &&) <$> hIsTerminalDevice stdin

    let srcName = case optsSource runOpts of
          SourceFile fp -> fp
          SourceStdin -> "«stdin»"
    src <- readSource (optsSource runOpts)

    -- When we read the source code from STDIN and STDIN + one of the output
    -- streams are terminal devices we output a seperating newline.
    void $ runMaybeT do
      guard inputIsTerm
      let checkOut h = do
            isTerm <- lift $ hIsTerminalDevice h
            guard isTerm
            lift $ hPutChar h '\n'
      checkOut stdout <|> checkOut stderr

    let mainModule = ModuleName "Main"
    let driverSettings =
          Driver.defaultSettings
            { driverSequential = optsDriverSeq runOpts,
              driverVerboseDeps = optsDriverDeps runOpts,
              driverVerboseSearches = optsDriverModSearch runOpts,
              driverSearchPaths = pure ".",
              driverOutputMode = stderrMode,
              driverOutputHandle = outputHandle
            }
            & Driver.addModuleSource mainModule srcName src

    checked <-
      maybe exitFailure pure =<< Driver.runDriver driverSettings do
        parsed <- Driver.parseAllModules mainModule
        uncurry Driver.checkAll parsed

    let isMain n =
          nameResolvedModule n == mainModule
            && nameUnqualified n == Unqualified "main"
    let mmainName = List.find isMain $ Map.keys $ moduleValues checked
    for_ mmainName \mainName -> do
      outputStrLn outputHandle "Running ‘main’"
      r <- I.runEval (I.programEnvironment checked) $ I.eval $ E.Var defaultPos mainName
      outputStrLn outputHandle $ "Result: " ++ show r
