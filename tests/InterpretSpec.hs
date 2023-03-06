{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}

module InterpretSpec (spec) where

import AlgST.Builtins
import AlgST.Driver qualified as Driver
import AlgST.Driver.Output
import AlgST.Interpret
import AlgST.Syntax.Module
import AlgST.Syntax.Name
import Data.HashMap.Strict qualified as HM
import Data.Map.Strict qualified as Map
import System.FilePath
import System.IO
import Test
import Test.Golden

spec :: Spec
spec = do
  describe "builtins environment" do
    it "contains definitions for all abstract builtins" do
      -- We don't export the builtinsEnv from AlgST.Interpret to avoid misuse.
      -- But we can recover it by providing an empty module to
      -- `programEnvironment`.
      let builtinsEnv = programEnvironment emptyModule
      let missingKeys = Map.keys $ moduleSigs builtinsModule Map.\\ builtinsEnv
      let message = "missing builtins:" : ["  " ++ pprName k | k <- missingKeys]
      null missingKeys @? unlines message

  describe "whole programs" do
    goldenTestsH dir \h inp -> do
      val <- compileAndRun h inp
      hPrint h val

compileAndRun :: Handle -> String -> Assertion Value
compileAndRun h src = do
  (output, mResultsGraph) <- captureOutput \outH -> do
    let settings =
          Driver.addModuleSource MainModule "" src $
            Driver.defaultSettings
              { -- All the different tests are run in parallel. Stay sequential here.
                Driver.driverSequential = True,
                Driver.driverOutputHandle = outH
              }
    Driver.runComplete settings
  resultsGraph <- mResultsGraph @? "Processing failed.\n\n" ++ output
  let allResults = Driver.compactResults resultsGraph
  mainResults <- HM.lookup MainModule allResults @? "›Main‹ module missing"
  mainName <- Driver.lookupRenamed MainFunction mainResults @? "›main‹ function missing"
  runEvalWith
    (defaultSettings {evalOutputHandle = h})
    (Driver.mergedResultEvalEnvironment allResults)
    (evalName mainName)

dir :: FilePath
dir = dropExtension __FILE__
