{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}

module InterpretSpec (spec) where

import AlgST.Builtins (builtins)
import AlgST.Interpret
import AlgST.Parse.Parser
import AlgST.Rename
import AlgST.Rename.Fresh
import AlgST.Syntax.Expression qualified as E
import AlgST.Syntax.Module
import AlgST.Syntax.Name
import AlgST.Typing
import AlgST.Util.Error
import Control.Category ((>>>))
import Control.Monad
import Data.List.NonEmpty (NonEmpty)
import Syntax.Base (defaultPos)
import System.FilePath
import Test.Golden
import Test.Hspec

spec :: Spec
spec = do
  -- TODO: I want to test that the 'AlgST.Interpret.builtinsEnv'
  -- contains definitions for all abstract builtins!
  describe "whole programs" do
    goldenTestsM
      dir
      (parseAndCheckProgram >>> shouldNotError >=> runProgram >>> fmap show)

shouldNotError :: (HasCallStack, Foldable f) => Either (f Diagnostic) a -> IO a
shouldNotError = \case
  Left errs -> expectationFailure (plainErrors errs) >> mzero
  Right a -> pure a

-- | Parses and typecheks a program in the context of 'declarations'.
parseAndCheckProgram :: String -> Either (NonEmpty Diagnostic) (Module Tc)
parseAndCheckProgram src = do
  parsed <- runParser (parseProg builtins) src
  runFresh (ModuleName "") $ runRename (renameModule parsed) >>= checkModule

runProgram :: TcModule -> IO Value
runProgram p = runEval env (eval mainExpr)
  where
    env = programEnvironment p
    mainExpr = E.Var defaultPos (Name (ModuleName "") (Unqualified "main"))

dir :: FilePath
dir = dropExtension __FILE__
