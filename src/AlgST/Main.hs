{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module AlgST.Main (main) where

import AlgST.Builtins
import AlgST.CommandLine
import AlgST.Driver (Settings (..))
import AlgST.Driver qualified as Driver
import AlgST.Driver.Dependencies (depsVertices)
import AlgST.Driver.Output
import AlgST.Interpret qualified as I
import AlgST.Parse.Parser qualified as P
import AlgST.Parse.Phase (Parse)
import AlgST.Rename
import AlgST.Syntax.Expression qualified as E
import AlgST.Syntax.Module
import AlgST.Syntax.Name
import AlgST.Syntax.Traversal
import AlgST.Typing (CheckContext, TcModule)
import AlgST.Typing qualified as Tc
import AlgST.Typing.Equality qualified as Eq
import AlgST.Util qualified as Util
import AlgST.Util.Error
import AlgST.Util.Output
import Control.Category ((>>>))
import Control.Exception
import Control.Monad
import Data.Bifunctor
import Data.DList.DNonEmpty qualified as DNE
import Data.Either
import Data.Foldable
import Data.Function
import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as HM
import Data.List qualified as List
import Data.List.NonEmpty (NonEmpty)
import Data.Map.Strict qualified as Map
import Data.Traversable
import Main.Utf8
import System.Console.ANSI qualified as ANSI
import System.Exit
import System.FilePath qualified as FP
import System.IO

mainModule :: ModuleName
mainModule = ModuleName "Main"

main :: IO ()
main = withUtf8 do
  runOpts <- getOptions
  stderrMode <- maybe (discoverMode stderr) pure (optsOutputMode runOpts)

  let allowAnsi = stderrMode /= Plain
  withOutput allowAnsi stderr \outputHandle -> do
    (renameEnvs, checkedModules) <- case optsSource runOpts of
      Nothing ->
        -- No custom source, only builtins.
        pure
          ( HM.singleton mainModule builtinsEnv,
            HM.singleton mainModule (builtinsModule, builtinsModuleCtxt)
          )
      Just src ->
        checkSources runOpts outputHandle stderrMode src
          >>= maybe exitFailure pure

    allGood <-
      answerQueries
        outputHandle
        stderrMode
        (optsQueries runOpts)
        renameEnvs
        (snd <$> checkedModules)
    runGood <-
      if optsDoEval runOpts
        then runInterpret outputHandle stderrMode (fst <$> checkedModules)
        else pure True
    when (not allGood || not runGood) do
      exitFailure

checkSources ::
  RunOpts ->
  OutputHandle ->
  OutputMode ->
  Source ->
  IO
    ( Maybe
        ( HashMap ModuleName RenameEnv,
          HashMap ModuleName (TcModule, CheckContext)
        )
    )
checkSources runOpts outH outMode mainSource = do
  mainSource <- case mainSource of
    SourceFile fp -> do
      Just . (FP.normalise fp,) <$> readFile' fp
    SourceStdin -> do
      -- If the input comes from the terminal and either of the output
      -- streams goes to the terminal we output a separating newline.
      stdinTerm <- hIsTerminalDevice stdin
      stdoutTerm <- hIsTerminalDevice stdout
      stderrTerm <- hIsTerminalDevice stderr
      let termOut
            | stdinTerm && stdoutTerm = Just stdout
            | stdinTerm && stderrTerm = Just stderr
            | otherwise = Nothing
      Just . ("«stdin»",)
        <$> getContents'
        <* for_ termOut \h -> hPutChar h '\n'
    SourceMain ->
      -- We expect the driver to find the Main module through its usual
      -- module lookup mechanism.
      pure Nothing

  let driverSettings =
        maybe id (uncurry (Driver.addModuleSource mainModule)) mainSource $
          Driver.defaultSettings
            { driverSequential = optsDriverSeq runOpts,
              driverVerboseDeps = optsDriverDeps runOpts,
              driverVerboseSearches = optsDriverModSearch runOpts,
              driverSearchPaths = FP.normalise <$> optsDriverPaths runOpts,
              driverOutputMode = outMode,
              driverOutputHandle = outH
            }

  mcheckResult <- Driver.runDriver driverSettings do
    (pathsMap, parsed) <- Driver.parseAllModules mainModule
    renamedEnv <- Driver.renameAll pathsMap parsed
    checkedCtxt <- Driver.checkAll pathsMap (fmap fst <$> renamedEnv)
    pure (renamedEnv, checkedCtxt)

  let results = do
        (renamedEnv, checkGraph) <- mcheckResult
        rnEnvs <- traverse (fmap snd) $ depsVertices renamedEnv
        checkRes <- sequence $ depsVertices checkGraph
        pure (rnEnvs, checkRes)
  outputLnS outH case results of
    Just _ -> applyStyle outMode (styleBold . styleFG ANSI.Green) (showString "Success.")
    Nothing -> applyStyle outMode (styleBold . styleFG ANSI.Red) (showString "Failed.")
  pure results

answerQueries ::
  OutputHandle ->
  OutputMode ->
  [Query] ->
  HashMap ModuleName RenameEnv ->
  HashMap ModuleName CheckContext ->
  IO Bool
answerQueries out outMode queries renameEnvs checkEnvs = do
  and <$> for queries \case
    QueryTySynth s ->
      parseRename P.parseExpr s tysynth
        & fmap showTySynth
        & printResult "--type" s
    QueryKiSynth s ->
      parseRename P.parseType s (fmap snd . Tc.kisynth)
        & fmap (pure . show)
        & printResult "--kind" s
    QueryNF s ->
      parseRename P.parseType s (Tc.kisynth >=> Tc.normalize . fst)
        & fmap (pure . show)
        & printResult "--nf" s
  where
    queryEnv = fold $ HM.lookup mainModule renameEnvs
    queryCtxt = fold $ HM.lookup mainModule checkEnvs

    tysynth expr = do
      t <- fmap snd $ Tc.tysynth expr
      tNF <- Tc.normalize t
      let !res
            | Eq.Alpha t == Eq.Alpha tNF = Left t
            | otherwise = Right (t, tNF)
      pure res

    showTySynth = either (pure . show) \(t, tNF) ->
      [ applyStyle outMode styleBold (showString "[SYN] ") (show t),
        applyStyle outMode styleBold (showString " [NF] ") (show tNF)
      ]

    parseRename ::
      SynTraversable (s Parse) Parse (s Rn) Rn =>
      P.Parser (s Parse) ->
      String ->
      (s Rn -> Tc.TypeM a) ->
      Either (NonEmpty Diagnostic) a
    parseRename p s f = do
      parsed <- P.runParser p s
      RenameExtra extra <-
        renameModuleExtra (ModuleName "Q") emptyModule
          & snd
          & ($ queryEnv)
          & first DNE.toNonEmpty
      first DNE.toNonEmpty $ extra \_ -> do
        renamed <- renameSyntax parsed
        Tc.checkResultAsRnM $ Tc.checkWithModule queryCtxt emptyModule \runTypeM _ ->
          runTypeM $ f renamed

    printResult :: String -> String -> Either (NonEmpty Diagnostic) [String] -> IO Bool
    printResult heading src = \case
      Left errs -> do
        outputLnS out $ prefix . renderErrors' (Just 5) outMode "" (toList errs)
        pure False
      Right lns -> do
        outputLnS out prefix
        sequence_ [outputLnS out $ showString $ "  " ++ s | s <- lns]
        pure True
      where
        prefix =
          showChar '\n'
            . applyStyle outMode (styleBold . styleFG ANSI.Cyan) (showString heading)
            . showChar ' '
            . applyStyle outMode (styleFG ANSI.Cyan) (showString (truncateSource src))

    truncateSource :: String -> String
    truncateSource =
      lines >>> \case
        [] -> ""
        [ln] -> Util.truncate' 60 "..." ln
        ln : _ -> take 60 ln ++ "..."

runInterpret :: OutputHandle -> OutputMode -> HashMap ModuleName TcModule -> IO Bool
runInterpret out outMode checkedModules = do
  let merge a b =
        Module
          { moduleTypes = moduleTypes a <> moduleTypes b,
            moduleValues = moduleValues a <> moduleValues b,
            moduleSigs = moduleSigs a <> moduleSigs b
          }
  let bigModule = foldl' merge builtinsModule checkedModules
  let mmainName = do
        mainChecked <- HM.lookup mainModule checkedModules
        moduleValues mainChecked
          & Map.keys
          & List.find ((Unqualified "main" ==) . nameUnqualified)
  let outputError =
        outputLnS out . applyStyle outMode (styleFG ANSI.Red) . showString
  outputStrLn out ""
  case mmainName of
    Nothing -> do
      outputError "No ‘main’ to run."
      pure False
    Just mainName -> do
      outputSticky out "Running ‘main’"
      result <- try do
        I.runEval (I.programEnvironment bigModule) $
          I.eval $ E.Var ZeroPos mainName
      clearSticky out
      case result of
        Left ex
          -- Don't catch async exceptions as these are usually not meant to be
          -- recoverable/we want to exit as fast as possible. For example,
          -- CTRL-C raises an async exception.
          | Just (_ :: SomeAsyncException) <- fromException ex -> throwIO ex
          | otherwise -> outputException out outMode "Running Failed" ex
        Right val ->
          outputLnS out $ applyStyle outMode styleBold (showString "Result: ") . shows val
      pure $ isRight result

outputException :: Exception e => OutputHandle -> OutputMode -> String -> e -> IO ()
outputException h m s e =
  outputLnS h $ header . showChar '\n' . showString (displayException e)
  where
    header =
      applyStyle m (styleBold . styleFG ANSI.Red) $
        showString "===== " . showString s . showString " ====="
