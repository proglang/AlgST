{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeFamilies #-}

module AlgST.Builtins.Names where

import AlgST.Syntax.Name

-- TODO: Change this to "Builtin" once proper name resolution is implemented.
pattern BuiltinsModule :: Module
pattern BuiltinsModule = Module ""

pattern Builtin :: String -> Name Written scope
pattern Builtin s = Name BuiltinsModule (Unqualified s)

pattern TypeInt :: TypeVar
pattern TypeInt = Builtin "Int"

pattern TypeChar :: TypeVar
pattern TypeChar = Builtin "Char"

pattern TypeString :: TypeVar
pattern TypeString = Builtin "String"

pattern TypeBool :: TypeVar
pattern TypeBool = Builtin "Bool"

pattern ConTrue, ConFalse :: ProgVar
pattern ConTrue = Builtin "True"
pattern ConFalse = Builtin "False"
