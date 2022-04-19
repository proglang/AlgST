{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}

module InterpretSpec (spec) where

import AlgST.Builtins (builtins)
import AlgST.Builtins.TH
import AlgST.Interpret
import AlgST.Parse.Parser
import AlgST.Parse.Phase
import AlgST.Rename
import AlgST.Syntax.Expression qualified as E
import AlgST.Syntax.Program
import AlgST.Syntax.Variable
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
  describe "whole programs" do
    goldenTestsM
      dir
      (parseAndCheckProgram >>> shouldNotError >=> runProgram >>> fmap show)

shouldNotError :: (HasCallStack, Foldable f) => Either (f Diagnostic) a -> IO a
shouldNotError = \case
  Left errs -> expectationFailure (plainErrors errs) >> mzero
  Right a -> pure a

-- | Parses and typecheks a program in the context of 'declarations'.
parseAndCheckProgram :: String -> Either (NonEmpty Diagnostic) (Program Tc)
parseAndCheckProgram src = do
  parsed <- runParser (parseProg declarations) src
  withRenamedProgram parsed checkProgram

runProgram :: TcProgram -> IO Value
runProgram p = runEval env (eval mainExpr)
  where
    env = programEnvironment p
    mainExpr = E.Var defaultPos (mkVar defaultPos "main")

-- | Declares some data types.
--
-- The basic 'builtins' are included.
declarations :: Program Parse
declarations =
  $$( let sigs =
            []
          decls =
            [ "data D0         = D0",
              "data D0'   : TU = D0'",
              "data D0_TL : TL = D0_TL",
              --
              "protocol P0      = P0",
              "protocol P0' : P = P0'",
              --
              "type Id_MU : MU (a:MU) = a",
              "type Id_TU : TU (a:TU) = a",
              "type Id_TL : TL (a:TL) = a",
              --
              "data     D3 (a:P) (b:SL) (c:TL) = D3",
              "protocol P3 (a:P) (b:SL) (c:TL) = P3",
              --
              "type Session (x:P) = forall (s:SL). ?x.s -> s",
              --
              "data AB = A | B"
            ]
       in parseStatic' builtins sigs decls
    )

dir :: FilePath
dir = dropExtension __FILE__
