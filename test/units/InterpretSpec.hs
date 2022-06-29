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
import AlgST.Util.Error
import AlgST.Util.Lenses
import Control.Category ((>>>))
import Control.Monad
import Data.Bifunctor
import Data.DList.DNonEmpty qualified as DNE
import Data.List.NonEmpty (NonEmpty)
import Data.Maybe
import Lens.Family2
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
      ( parseAndCheckProgram
          >>> shouldNotError
          >=> uncurry runProgram
          >>> fmap show
      )

shouldNotError :: (HasCallStack, Foldable f) => Either (f Diagnostic) a -> IO a
shouldNotError = \case
  Left errs -> expectationFailure (plainErrors errs) >> mzero
  Right a -> pure a

parseAndCheckProgram :: String -> Either (NonEmpty Diagnostic) (NameR Values, Module Tc)
parseAndCheckProgram src = do
  parsed <- runParser parseDecls src
  let name = ModuleName "M"
  let (mm, rnExtra) = renameModuleExtra name parsed
  tcModule <- first DNE.toNonEmpty do
    RenameExtra rn <- rnExtra builtinsEnv
    rn (checkResultAsRnM . checkModule builtinsModuleCtxt)
  let mainName =
        error "program has no ‘main’."
          `fromMaybe` (modMapValues mm ^. _TopLevels . hashAt (Unqualified "main"))
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
