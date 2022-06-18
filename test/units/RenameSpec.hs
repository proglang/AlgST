{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}

module RenameSpec (spec) where

import AlgST.Builtins
import AlgST.Parse.Parser
import AlgST.Rename
import AlgST.Rename.Error (AmbiguousOrigin (..))
import AlgST.Rename.Fresh
import AlgST.Rename.Modules
import AlgST.Syntax.Name
import AlgST.Syntax.Tree
import Control.Monad.Reader
import Control.Monad.Validate
import Data.Bifunctor
import Data.Function
import Data.Map.Strict qualified as Map
import Data.Traversable
import Syntax.Base
import System.FilePath
import Test.Golden
import Test.Hspec

spec :: Spec
spec = do
  describe "valid" do
    describe "expressions" do
      goldenTests (dir "valid/expr") parseRenameExpr

    describe "declarations" do
      goldenTests (dir "valid/prog") do
        -- TODO: Verify the resulting module map as well.
        runParserSimple parseDecls
          >=> bimap plainErrors drawLabeledTree
            . renameModule (ModuleName "M") renameEnv

  describe "invalid" do
    describe "expressions" do
      goldenTests
        (dir "invalid/expr")
        (swap . parseRenameExpr)

parseRenameExpr :: String -> Either String String
parseRenameExpr src = do
  expr <- runParserSimple parseExpr src
  renameSyntax expr
    & runValidateT
    & flip runReaderT (emptyModuleMap, renameEnv)
    & runFresh (ModuleName "M")
    & bimap plainErrors drawLabeledTree

renameEnv :: RenameEnv
renameEnv =
  builtinsEnv
    <> RenameEnv
      { rnTyVars = mconcat types,
        rnProgVars = mconcat values
      }
  where
    (rid, values) =
      mapAccumL binding firstResolvedId . fmap Unqualified $
        [ "global",
          "C1",
          "C2"
        ]
    (_, types) =
      mapAccumL binding rid . fmap Unqualified $
        []
    binding :: ResolvedId -> Unqualified -> (ResolvedId, Bindings scope)
    binding !rid u = do
      let n = Name emptyModuleName u
      let resolved =
            PartialResolve $
              Map.singleton
                (ResolvedName n (ModuleName "R") rid)
                (AmbiguousDefine defaultPos)
      (nextResolvedId rid, Bindings (Map.singleton n resolved))

dir :: FilePath -> FilePath
dir sub = dropExtension __FILE__ </> sub
