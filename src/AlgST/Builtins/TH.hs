{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -fno-defer-type-errors #-}

module AlgST.Builtins.TH where

import AlgST.Parse.Parser
import AlgST.Rename
import AlgST.Syntax.Decl
import AlgST.Syntax.Module
import AlgST.Syntax.Name
import AlgST.Typing
import AlgST.Util.Error
import Control.Monad.Eta
import Control.Monad.Trans
import Control.Monad.Validate
import Data.Foldable
import Language.Haskell.TH hiding (Name)
import Language.Haskell.TH.CodeDo qualified as Code

parseTH ::
  Globals -> ModuleName -> ModuleMap -> [String] -> CodeQ (ModuleMap, CheckContext, TcModule)
parseTH globals modName baseMap srcLines = Code.do
  parsed <- case runParserSimple parseModule (unlines srcLines) of
    Left err -> do
      reportError $ "parse error:" ++ err
      pure $ ParsedModule [] emptyModule
    Right p -> do
      pure p
  let (modmap, resolve) = continueRenameExtra baseMap modName parsed
  let check renamed = do
        let markBuiltin = \case
              DataDecl _ decl -> DataDecl OriginBuiltin decl
              decl -> decl
        let builtinRenamed = renamed {moduleTypes = markBuiltin <$> moduleTypes renamed}
        let doCheck = checkWithModule mempty builtinRenamed \runTypeM checked ->
              (checked,) <$> runTypeM extractCheckContext
        mapErrors runErrors $ mapValidateT lift doCheck
  let checked = runValidate (resolve globals) >>= \(RenameExtra f) -> f check
  case checked of
    Left errs -> Code.do
      traverse_ (reportError . tail . formatErrorMessages Plain "") errs
      [||(modmap, mempty, emptyModule)||]
    Right (tcmod, ctxt) ->
      [||(modmap, ctxt, tcmod)||]
