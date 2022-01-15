{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}

module RenameSpec (spec) where

import Data.Bifunctor
import AlgST.Builtins (builtins)
import AlgST.Builtins.TH
import AlgST.Parse.Parser
import AlgST.Parse.Phase
import AlgST.Rename
import AlgST.Syntax.Program
import AlgST.Syntax.Tree
import System.FilePath
import Test.Golden
import Test.Hspec

spec :: Spec
spec = do
  describe "valid" do
    describe "expressions" do
      goldenTests (dir "valid/expr") parseRenameExpr

    describe "programs" do
      goldenTests (dir "valid/prog") \src -> do
        p <- runParserSimple (parseProg knownGlobals) src
        bimap plainErrors drawNoBuiltins $ withRenamedProgram p pure

  describe "invalid" do
    let swap = \case
          Left x -> Right x
          Right x -> Left x

    describe "expressions" do
      goldenTests (dir "invalid/expr") $ swap . parseRenameExpr

    describe "programs" do
      goldenTests (dir "invalid/prog") \src -> swap do
        p <- runParserSimple (parseProg knownGlobals) src
        bimap plainErrors drawNoBuiltins $ withRenamedProgram p pure

knownGlobals :: PProgram
knownGlobals =
  -- The types don't really matter but we have to write something.
  $$( let sigs =
            [(,) "global" "()"]
          decls =
            ["data T = C1 | C2"]
       in parseStatic' builtins sigs decls
    )

drawNoBuiltins :: RnProgram -> String
drawNoBuiltins p = drawLabeledTree $ p `withoutProgramDefinitions` knownGlobals

parseRenameExpr :: String -> Either String String
parseRenameExpr src = do
  expr <- runParserSimple parseExpr src
  bimap plainErrors drawLabeledTree $ runRename knownGlobals $ renameSyntax expr

dir :: FilePath -> FilePath
dir sub = dropExtension __FILE__ </> sub
