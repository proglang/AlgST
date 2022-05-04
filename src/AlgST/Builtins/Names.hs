{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeFamilies #-}

module AlgST.Builtins.Names where

import AlgST.Syntax.Name

-- TODO: Change this to "Builtin" once proper name resolution is implemented.
pattern BuiltinsModule :: Module
pattern BuiltinsModule = Module ""

pattern Builtin :: String -> NameW scope
pattern Builtin s = Name BuiltinsModule (Unqualified s)

pattern TypeInt :: NameW Types
pattern TypeInt = Builtin "Int"

pattern TypeChar :: NameW Types
pattern TypeChar = Builtin "Char"

pattern TypeString :: NameW Types
pattern TypeString = Builtin "String"

pattern TypeBool :: NameW Types
pattern TypeBool = Builtin "Bool"

pattern ConTrue, ConFalse :: NameW Values
pattern ConTrue = Builtin "True"
pattern ConFalse = Builtin "False"
