module AlgST.Main (main) where

import AlgST.Builtins (builtinsModule)
import AlgST.CommandLine
import AlgST.Driver (Settings (..))
import AlgST.Driver qualified as Driver
import AlgST.Driver.Dependencies (depsVertices)
import AlgST.Driver.Output
import AlgST.Interpret qualified as I
import AlgST.Syntax.Expression qualified as E
import AlgST.Syntax.Module
import AlgST.Syntax.Name
import AlgST.Util.Output
import Control.Applicative
import Control.Monad
import Control.Monad.Reader
import Control.Monad.Trans.Maybe
import Data.Foldable
import Data.Function
import Data.HashMap.Strict qualified as HM
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
              driverSearchPaths = optsDriverPaths runOpts,
              driverOutputMode = stderrMode,
              driverOutputHandle = outputHandle
            }
            & Driver.addModuleSource mainModule srcName src

    mcheckedGraph <- Driver.runDriver driverSettings do
      (pathsMap, parsed) <- Driver.parseAllModules mainModule
      renamed <- Driver.renameAll pathsMap parsed
      Driver.checkAll pathsMap renamed

    checkedModules <- maybe exitFailure pure do
      checkedGraph <- mcheckedGraph
      sequence $ depsVertices checkedGraph

    -- Merge all the modules.
    let merge a b =
          Module
            { moduleTypes = moduleTypes a <> moduleTypes b,
              moduleValues = moduleValues a <> moduleValues b,
              moduleSigs = moduleSigs a <> moduleSigs b
            }
    -- Begin merging from the builtins module.
    let bigModule = foldl' merge builtinsModule checkedModules
    let mmainName = do
          mainChecked <- HM.lookup mainModule checkedModules
          moduleValues mainChecked
            & Map.keys
            & List.find ((Unqualified "main" ==) . nameUnqualified)

    mainName <- case mmainName of
      Nothing -> do
        outputStrLn outputHandle "Success. No ‘main’ to run."
        exitSuccess
      Just n -> do
        pure n

    outputSticky outputHandle "Running ‘main’"
    r <- I.runEval (I.programEnvironment bigModule) $ I.eval $ E.Var defaultPos mainName
    clearSticky outputHandle
    outputStrLn outputHandle $ "Result: " ++ show r
