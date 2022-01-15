{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
module AlgST.Parse.Read where

import           AlgST.Parse.Parser
import           AlgST.Parse.Phase
import           AlgST.Syntax.Kind

instance Read Kind where
  readsPrec _ = readParser parseKind

instance Read PType where
  readsPrec _ = readParser parseType

instance Read PExp where
  readsPrec _ = readParser parseExpr

readParser :: Parser a -> String -> [(a, String)]
readParser p str =
  case runParserSimple p str of
    Left _ -> []
    Right a -> [(a, "")]
