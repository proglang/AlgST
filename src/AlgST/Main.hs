module AlgST.Main (main) where

import Control.Applicative
import Control.DeepSeq
import Control.Exception
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Maybe
import Data.Foldable
import Data.Maybe
import AlgST.Builtins (builtins)
import AlgST.CommandLine
import AlgST.Parse.Parser
import AlgST.Rename
import AlgST.Typing
import AlgST.Util.Error
import AlgST.Util.Output
import System.Console.ANSI
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

  -- Force the input completely so that the output does not overlap.
  inputIsTerm <- (isNothing (optsSourceFile runOpts) &&) <$> hIsTerminalDevice stdin
  lazySrc <- maybe getContents readFile (optsSourceFile runOpts)
  src <- evaluate $!! lazySrc

  -- When we read the source code from STDIN and STDIN + one of the output
  -- streams are terminal devices we output a seperating newline.
  void $ runMaybeT do
    guard inputIsTerm
    let checkOut h = do
          isTerm <- lift $ hIsTerminalDevice h
          guard isTerm
          lift $ hPutChar h '\n'
    checkOut stdout <|> checkOut stderr

  parsed <- runStage opts "Parsing" $ runParser (parseProg builtins) src
  _checked <- runStage opts "Checking" $ withRenamedProgram parsed checkProgram
  pure ()

runStage :: Options -> String -> Either [PosError] a -> IO a
runStage opts stage res = do
  let info = style [SetColor Foreground Vivid Cyan]
  let success = style [SetColor Foreground Dull Green]
  let failure = style [SetColor Foreground Dull Red] . styleBold

  let styled selector f s = applyStyle (selector opts) f (showString s) ""
  putStr $ styled stdoutMode info $ stage ++ " ... "
  hFlush stdout

  case res of
    Left errs -> do
      putStrLn $ styled stdoutMode failure "failed"
      hPutStrLn stderr $
        renderErrors
          (stderrMode opts)
          (fold $ optsSourceFile $ runOpts opts)
          errs
      exitFailure
    Right a -> do
      putStrLn $ styled stdoutMode success "ok"
      pure a
