{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
{-# OPTIONS_GHC -fno-defer-type-errors #-}

module AlgST.Builtins.TH where

import AlgST.Builtins.Names
import AlgST.Parse.Parser
import AlgST.Parse.Phase
import AlgST.Syntax.Decl
import AlgST.Syntax.Module
import AlgST.Syntax.Name
import AlgST.Util
import Control.Monad
import Data.List.NonEmpty (nonEmpty)
import Data.Map.Strict qualified as Map
import Data.Maybe
import Data.Set qualified as Set
import Language.Haskell.TH hiding (Name)
import Language.Haskell.TH.CodeDo qualified as Code

parseStatic :: [(String, String)] -> [String] -> CodeQ PModule
parseStatic = parseStatic' emptyModule

parseStatic' :: PModule -> [(String, String)] -> [String] -> CodeQ PModule
parseStatic' baseProg sigs lines = Code.do
  let showVar :: Name stage scope -> String
      showVar a = "‘" ++ pprName a ++ "’"
  let parseSig (name, sig) = do
        case runParserSimple parseType sig of
          Left err -> do
            reportError $ "Can't parse signature of ‘" ++ name ++ "’:" ++ err
            pure Nothing
          Right ty -> do
            pure $ Just (Builtin name, ty)
  let addSig sigsMap (name, sig)
        | name `Map.member` sigsMap = do
          reportError $ "Multiple definitions of " ++ showVar name
          pure sigsMap
        | otherwise = do
          let sigDecl = SignatureDecl OriginBuiltin sig
          pure $! Map.insert name sigDecl sigsMap
  parsedSigs <- catMaybes <$> traverse parseSig sigs
  sigsMap <- foldM addSig mempty parsedSigs

  prog <- case runParserSimple (parseProg baseProg) (unlines lines) of
    Left err -> do
      reportError $ "Module failed to parse:" ++ err
      pure emptyModule
    Right p -> do
      pure p

  let (merged, conflict1, conflict2) =
        mergeModules prog emptyModule {moduleSigs = sigsMap}
      conflicts =
        nonEmpty $ fmap showVar (Set.toList conflict1) ++ fmap showVar (Set.toList conflict2)
  whenJust conflicts \conflicts ->
    reportError $ "Multiple definitions of " ++ joinAnd conflicts
  [||merged||]
