module AlgST.Main (main) where

import AlgST.CommandLine
import AlgST.Driver qualified as Driver
import AlgST.Syntax.Name
import AlgST.Util.Error
import AlgST.Util.Output
import Control.Applicative
import Control.Monad
import Control.Monad.Reader
import Control.Monad.Trans.Maybe
import Data.Function
import Data.Maybe
import System.Exit
import System.IO

data Options = Options
  { runOpts :: !RunOpts,
    stdoutMode :: !OutputMode,
    stderrMode :: !OutputMode
  }

main :: IO ()
main = do
  runOpts <- getOptions
  opts <-
    Options runOpts
      <$> maybe (discoverMode stdout) pure (optsOutputMode runOpts)
      <*> maybe (discoverMode stderr) pure (optsOutputMode runOpts)

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
          & Driver.addSearchPathFront "."
          & Driver.enableDebugMessages True
          & Driver.addModuleSource mainModule srcName src

  res <- Driver.runDriver (stdoutMode opts) driverSettings do
    parsed <- Driver.parseAllModules mainModule
    uncurry Driver.checkAll parsed
  when (isNothing res) do
    exitFailure

  -- TODO: Run Main.main if defined.
  pure ()
