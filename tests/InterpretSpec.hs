{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}

module InterpretSpec (spec) where

import AlgST.Builtins
import AlgST.Interpret
import AlgST.Parse.Parser
import AlgST.Rename
import AlgST.Rename.Modules
import AlgST.Syntax.Expression qualified as E
import AlgST.Syntax.Module
import AlgST.Syntax.Name
import AlgST.Typing
import AlgST.Util.Lenses
import Control.Monad
import Lens.Family2
import System.FilePath
import Test
import Test.Golden

spec :: Spec
spec = do
  -- TODO: I want to test that the 'AlgST.Interpret.builtinsEnv'
  -- contains definitions for all abstract builtins!
  describe "whole programs" do
    goldenTests dir do
       parseAndCheckProgram
          >=> uncurry runProgram
          >>> fmap show

parseAndCheckProgram :: String -> Assertion (NameR Values, Module Tc)
parseAndCheckProgram src = do
  parsed <- shouldParse parseDecls src
  let name = ModuleName "M"
  let (mm, rnExtra) = renameModuleExtra name parsed
  tcModule <- shouldNotError do
    RenameExtra rn <- rnExtra builtinsEnv
    rn (checkResultAsRnM . checkModule builtinsModuleCtxt)
  mainName <- failNothing "program has no ‘main’" $
    modMapValues mm ^. _TopLevels . hashAt (Unqualified "main")
  pure (mainName, tcModule)

runProgram :: NameR Values -> TcModule -> IO Value
runProgram mainName p = runEval env (eval mainExpr)
  where
    env = programEnvironment $ merge p builtinsModule
    mainExpr = E.Var ZeroPos mainName
    merge a b =
      Module
        { moduleTypes = moduleTypes a <> moduleTypes b,
          moduleValues = moduleValues a <> moduleValues b,
          moduleSigs = moduleSigs a <> moduleSigs b
        }

dir :: FilePath
dir = dropExtension __FILE__
