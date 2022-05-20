{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
{-# OPTIONS_GHC -fno-defer-type-errors #-}

module AlgST.Builtins.TH where

import AlgST.Parse.Parser
import AlgST.Rename
import AlgST.Syntax.Name
import AlgST.Syntax.Program
import AlgST.Util.Error
import Data.Foldable
import Language.Haskell.TH hiding (Name)
import Language.Haskell.TH.CodeDo qualified as Code

parseTH :: Globals -> ModuleName -> ModuleMap -> [String] -> CodeQ (ModuleMap, RnModule)
parseTH globals modName baseMap srcLines = Code.do
  parsed <- case runParserSimple parseModule (unlines srcLines) of
    Left err -> do
      reportError $ "parse error:" ++ err
      pure emptyModule
    Right p -> do
      pure p
  let (modmap, resolve) = continueRenameExtra baseMap modName parsed
  renamed <- case renameSimple globals resolve of
    Left errs -> do
      traverse_ (reportError . tail . formatErrorMessages Plain "") errs
      pure emptyModule
    Right m ->
      pure m
  [||(modmap, renamed)||]
