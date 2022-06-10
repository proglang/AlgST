{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}

module RenameSpec (spec) where

import AlgST.Parse.Parser
import AlgST.Rename
import AlgST.Rename.Fresh
import AlgST.Rename.Modules
import AlgST.Syntax.Name
import AlgST.Syntax.Tree
import Control.Monad.Reader
import Control.Monad.Validate
import Data.Bifunctor
import Data.Function
import System.FilePath
import Test.Golden
import Test.Hspec

spec :: Spec
spec = do
  describe "expressions" do
    goldenTests (dir "expr") parseRenameExpr

  describe "declarations" do
    goldenTests (dir "prog") do
      -- TODO: Verify the resulting module map as well.
      runParserSimple parseDecls
        >=> bimap plainErrors drawLabeledTree
          . renameModule (ModuleName "M") mempty

parseRenameExpr :: String -> Either String String
parseRenameExpr src = do
  expr <- runParserSimple parseExpr src
  renameSyntax expr
    & runValidateT
    & flip runReaderT (emptyModuleMap, mempty)
    & runFresh (ModuleName "M")
    & bimap plainErrors drawLabeledTree

dir :: FilePath -> FilePath
dir sub = dropExtension __FILE__ </> sub
