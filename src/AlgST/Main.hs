{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}

module AlgST.Main (main) where

import AlgST.Builtins (builtinsModule)
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
import AlgST.Util qualified as Util
import AlgST.Util.Error
import AlgST.Util.Output
import Control.Category ((>>>))
import Control.Monad
import Data.Bifunctor
import Data.DList.DNonEmpty qualified as DNE
import Data.Foldable
import Data.Function
import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as HM
import Data.List qualified as List
import Data.List.NonEmpty (NonEmpty)
import Data.Map.Strict qualified as Map
import Data.Traversable
import Syntax.Base
import System.Exit
import System.FilePath qualified as FP
import System.IO

mainModule :: ModuleName
mainModule = ModuleName "Main"

main :: IO ()
main = do
  runOpts <- getOptions
  stderrMode <- maybe (discoverMode stderr) pure (optsOutputMode runOpts)

  let allowAnsi = stderrMode /= Plain
  withOutput allowAnsi stderr \outputHandle -> do
    mainSource <- case optsSource runOpts of
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
                driverOutputMode = stderrMode,
                driverOutputHandle = outputHandle
              }

    mcheckResult <- Driver.runDriver driverSettings do
      (pathsMap, parsed) <- Driver.parseAllModules mainModule
      renamedEnv <- Driver.renameAll pathsMap parsed
      checkedCtxt <- Driver.checkAll pathsMap (fmap fst <$> renamedEnv)
      pure (renamedEnv, checkedCtxt)

    (renameEnvs, checkedModules) <- maybe exitFailure pure do
      (renamedEnv, checkGraph) <- mcheckResult
      rnEnvs <- traverse (fmap snd) $ depsVertices renamedEnv
      checkRes <- sequence $ depsVertices checkGraph
      pure (rnEnvs, checkRes)
    outputStrLn outputHandle "Success."

    allGood <-
      answerQueries
        outputHandle
        stderrMode
        (optsQueries runOpts)
        renameEnvs
        (snd <$> checkedModules)
    runInterpret
      outputHandle
      (fst <$> checkedModules)

    when (not allGood) do
      exitFailure

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
      parseRename P.parseExpr s (fmap snd . Tc.tysynth)
        & printResult "--type" s
    QueryKiSynth s ->
      parseRename P.parseType s (fmap snd . Tc.kisynth)
        & printResult "--kind" s
    QueryNF s ->
      parseRename P.parseType s (Tc.kisynth >=> Tc.normalize . fst)
        & printResult "--nf" s
  where
    queryEnv = fold $ HM.lookup mainModule renameEnvs
    queryCtxt = fold $ HM.lookup mainModule checkEnvs

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

    printResult :: Show a => String -> String -> Either (NonEmpty Diagnostic) a -> IO Bool
    printResult heading src = \case
      Left errs -> do
        outputS out $ prefix . renderErrors' (Just 5) outMode "" (toList errs)
        pure False
      Right a -> do
        outputLnS out prefix
        outputLnS out $ showString "  " . shows a
        pure True
      where
        prefix =
          showChar '\n'
            . applyStyle outMode styleBold (showString heading)
            . showChar ' '
            . showString (truncateSource src)

    truncateSource :: String -> String
    truncateSource =
      lines >>> \case
        [] -> ""
        [ln] -> Util.truncate' 60 "..." ln
        ln : _ -> take 60 ln ++ "..."

runInterpret :: OutputHandle -> HashMap ModuleName TcModule -> IO ()
runInterpret out checkedModules = do
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

  case mmainName of
    Nothing -> do
      outputStrLn out "\nNo ‘main’ to run."
    Just mainName -> do
      outputSticky out "Running ‘main’"
      result <-
        I.runEval (I.programEnvironment bigModule) $
          I.eval $ E.Var defaultPos mainName
      clearSticky out
      outputStrLn out $ "Result: " ++ show result
