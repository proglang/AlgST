{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}

module RenameSpec (spec) where

import AlgST.Builtins (builtins)
import AlgST.Parse.Parser
import AlgST.Rename
import AlgST.Syntax.Program
import AlgST.Syntax.Tree
import System.FilePath
import Test.Golden
import Test.Hspec

spec :: Spec
spec = do
  describe "expressions" do
    goldenTests (dir "expr") parseRenameExpr

  describe "programs" do
    goldenTests (dir "prog") \src -> do
      p <- runParserSimple (parseProg builtins) src
      pure $ drawNoBuiltins $ withRenamedProgram p pure

drawNoBuiltins :: RnProgram -> String
drawNoBuiltins p = drawLabeledTree $ p `withoutProgramDefinitions` builtins

parseRenameExpr :: String -> Either String String
parseRenameExpr src = do
  expr <- runParserSimple parseExpr src
  pure $ drawLabeledTree $ runRename $ renameSyntax expr

dir :: FilePath -> FilePath
dir sub = dropExtension __FILE__ </> sub
