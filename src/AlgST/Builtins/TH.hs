{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -fno-defer-type-errors #-}

module AlgST.Builtins.TH where

import Control.Monad
import Data.List.NonEmpty (nonEmpty)
import qualified Data.Map.Strict as Map
import Data.Maybe
import qualified Data.Set as Set
import Language.Haskell.TH
import AlgST.Parse.Parser
import AlgST.Parse.Phase
import AlgST.Syntax.Decl
import AlgST.Syntax.Program
import AlgST.Util
import Syntax.Base
import Syntax.ProgramVariable

parseStatic :: [(String, String)] -> [String] -> TExpQ PProgram
parseStatic = parseStatic' emptyProgram

parseStatic' :: PProgram -> [(String, String)] -> [String] -> TExpQ PProgram
parseStatic' baseProg sigs lines = do
  let showVar :: Show a => a -> String
      showVar a = "‘" ++ show a ++ "’"
  let parseSig (name, sig) = do
        case runParserSimple parseType sig of
          Left err -> do
            reportError $ "Can't parse signature of ‘" ++ name ++ "’:" ++ err
            pure Nothing
          Right ty -> do
            pure $ Just (mkVar defaultPos name :: ProgVar, ty)
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
      reportError $ "Program failed to parse:" ++ err
      pure emptyProgram
    Right p -> do
      pure p

  let (merged, conflict1, conflict2) =
        mergePrograms prog emptyProgram {programImports = sigsMap}
      conflicts =
        nonEmpty $ fmap showVar (Set.toList conflict1) ++ fmap showVar (Set.toList conflict2)
  whenJust conflicts \conflicts ->
    reportError $ "Multiple definitions of " ++ joinAnd conflicts
  [||merged||]
