{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module AlgST.Builtins.Names where

import AlgST.Builtins.TH2
import AlgST.Syntax.Name
import Data.Char qualified as C

$( runDefines (ModuleName "Builtin") "builtinsModuleMap" do
     let prefix p s = p ++ C.toUpper (head s) : tail s
     let typ x = defineType (prefix "type" x) (Unqualified x)
     let con x = defineValue (prefix "con" x) (Unqualified x)
     let val x = defineValue (prefix "val" x) (Unqualified x)
     let op n x = defineValue (prefix "op" n) $ Unqualified $ "(" ++ x ++ ")"

     defineValue "conPair" $ Unqualified "(,)"

     typ "Int"
     typ "Char"
     typ "String"

     typ "Bool"
     con "True"
     con "False"

     op "add" "+"
     op "sub" "-"
     op "mul" "*"
     op "div" "/"
     op "mod" "%"
     op "LEQ" "<="

     val "send"
     val "receive"
 )

pattern BuiltinsModule :: ModuleName
pattern BuiltinsModule = ModuleName "Builtin"
