{-# LANGUAGE RankNTypes #-}

module AlgST.Main (main) where

import AlgST.Builtins (builtins)
import AlgST.CommandLine
import AlgST.Parse.Parser
import AlgST.Parse.Phase
import AlgST.Rename
import AlgST.Typing
import AlgST.Util.Error
import AlgST.Util.Output
import Control.Applicative
import Control.DeepSeq
import Control.Exception
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Maybe
import Data.Foldable
import Data.Traversable.WithIndex
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

  inputIsTerm <- (sourceIsTerm (optsSource runOpts) &&) <$> hIsTerminalDevice stdin
  -- Force the input completely so that the output and remaining input do not
  -- overlap. This is only "required" in the case when reading from STDIN but
  -- should be alright for all the toy files to force always.
  src <- evaluate . force =<< readSource (optsSource runOpts)

  -- When we read the source code from STDIN and STDIN + one of the output
  -- streams are terminal devices we output a seperating newline.
  void $ runMaybeT do
    guard inputIsTerm
    let checkOut h = do
          isTerm <- lift $ hIsTerminalDevice h
          guard isTerm
          lift $ hPutChar h '\n'
    checkOut stdout <|> checkOut stderr

  mparsed <- runStage opts "Parsing" $ runParser (parseProg builtins) src
  runChecks opts =<< maybe exitFailure pure mparsed
  pure ()

runChecks :: Options -> PProgram -> IO ()
runChecks opts pprogram = do
  actions <- runStage opts "Checking" $
    withRenamedProgram pprogram \rnProgram ->
      checkWithProgram rnProgram \runTy runKi _ -> do
        Right <$> itraverse (evalAction opts runTy runKi) (optsActions (runOpts opts))
  oks <- sequence =<< maybe exitFailure pure actions
  when (not (and oks)) do
    exitFailure

evalAction :: Options -> RunTyM -> RunKiM -> Int -> Action -> RnM (IO Bool)
evalAction opts runTy runKi i = \case
  ActionNF src -> do
    let ptype = runParser parseType src
    rnty <- traverse renameSyntax ptype
    nfty <- join <$> traverse (runKi . (normalize . fst <=< kisynth)) rnty
    buildIO i "normal form" ((,) <$> ptype <*> nfty) \(ty, tynf) -> do
      print ty
      putStrLn $ "  => " ++ show tynf
  ActionKiSynth src -> do
    let ptype = runParser parseType src
    rnty <- traverse renameSyntax ptype
    kind <- join <$> traverse (runKi . fmap snd . kisynth) rnty
    buildIO i "kind synthesis" ((,) <$> ptype <*> kind) \(ty, k) -> do
      print ty
      putStrLn $ "  => " ++ show k
  ActionTySynth src -> do
    let pexp = runParser parseExpr src
    rnexp <- traverse renameSyntax pexp
    expty <- join <$> traverse (runKi . runTy . fmap snd . tysynth) rnexp
    buildIO i "type synthesis" ((,) <$> pexp <*> expty) \(e, ty) -> do
      print e
      putStrLn $ "  => " ++ show ty
  where
    -- Reset the source file. Otherwise the main source gets blamed for errors
    -- in the action sources.
    modifyOpts o =
      o {runOpts = (runOpts o) {optsSource = SourceStdin}}
    buildIO i desc errsOrA f = pure do
      ma <- runStage (modifyOpts opts) ("\n[" ++ show (i + 1) ++ "] " ++ desc) errsOrA
      case ma of
        Just a -> True <$ f a
        Nothing -> pure False

runStage :: Foldable f => Options -> String -> Either (f PosError) a -> IO (Maybe a)
runStage opts stage res = do
  let info = style [SetColor Foreground Vivid Cyan]
  let success = style [SetColor Foreground Dull Green]
  let failure = style [SetColor Foreground Dull Red] . styleBold

  let styled selector f s = applyStyle (selector opts) f (showString s) ""
  let putStatus style msg =
        putStr $ styled stdoutMode style msg
  putStatus info $ stage ++ " ... "
  hFlush stdout

  case res of
    Left errs -> do
      putStatus failure "failed\n"
      hPutStrLn stderr $
        renderErrors
          (stderrMode opts)
          (fold $ sourcePrettyName $ optsSource $ runOpts opts)
          (toList errs)
      pure Nothing
    Right a -> do
      putStatus success "ok\n"
      pure $ Just a
