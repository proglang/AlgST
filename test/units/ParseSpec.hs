{-# LANGUAGE CPP #-}
{-# LANGUAGE ImplicitParams #-}

module ParseSpec (spec) where

import AlgST.Parse.Parser
import AlgST.Syntax.Tree
import System.FilePath
import Test.Golden
import Test.Hspec

spec :: Spec
spec = do
  describe "valid" do
    describe "expressions" do
      goldenTests
        (dir "valid/expr")
        (parseTree parseExpr)

    describe "types" do
      goldenTests
        (dir "valid/type")
        (parseTree parseType)

    describe "declarations" do
      goldenTests
        (dir "valid/decl")
        (parseTree parseModule)

  describe "invalid" do
    describe "expressions" do
      goldenTests
        (dir "invalid/expr")
        (swap . parseTree parseExpr)

    describe "declarations" do
      goldenTests
        (dir "invalid/decl")
        (swap . parseTree parseModule)

    -- These tests will probably be dropped.
    describe "declarations + builtins" do
      goldenTests
        (dir "invalid/decl+builtins")
        (swap . parseTree parseModule)

  describe "associativity" do
    specify "type application" do
      let ?parser = parseType
      "A b c" `shouldParseLike` "((A b) c)"

parseTree :: LabeledTree a => Parser a -> String -> Either String String
parseTree p src = drawLabeledTree <$> runParserSimple p src

shouldParseLike :: (?parser :: Parser a, LabeledTree a) => String -> String -> Expectation
shouldParseLike src1 src2 =
  parseTree ?parser src1 `shouldBe` parseTree ?parser src2

dir :: FilePath -> FilePath
dir sub = dropExtension __FILE__ </> sub
