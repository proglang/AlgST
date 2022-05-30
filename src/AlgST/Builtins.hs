{-# LANGUAGE TemplateHaskell #-}

module AlgST.Builtins
  ( module AlgST.Builtins.Names,
    builtinsImport,
    builtinsModule,
    builtinsModuleMap,
    builtinsModuleCtxt,
  )
where

import AlgST.Builtins.Names hiding (builtinsPartialModuleMap)
import AlgST.Builtins.Names qualified as B
import AlgST.Builtins.TH
import AlgST.Rename (ModuleMap)
import AlgST.Syntax.Module
import AlgST.Syntax.Name
import AlgST.Typing qualified as Tc
import AlgST.Typing.Phase (TcModule)
import Syntax.Base

builtinsImport :: Import
builtinsImport =
  Import
    { importTarget = BuiltinsModule,
      importQualifier = emptyModuleName,
      importSelection = ImportAll defaultPos mempty mempty
    }

builtinsModule :: TcModule
builtinsModuleMap :: ModuleMap
builtinsModuleCtxt :: Tc.CheckContext
(builtinsModuleMap, builtinsModuleCtxt, builtinsModule) =
  $$( let defs =
            [ "data String : MU",
              "data Char : MU",
              "data Int : MU",
              "data Bool = True | False",
              --
              "negate : Int -> Int",
              "negate n = 0 - n",
              --
              "(|>) : ∀(a:TL). ∀(b:TL). a -> (a -o b) -o b",
              "(|>) x f = f x",
              --
              "(<|) : ∀(a:TL). ∀(b:TL). (a -o b) -> a -o b",
              "(<|) f x = f x",
              --
              "not : Bool -> Bool",
              "not b = if b then False else True",
              --
              "(&&) : Bool -> Bool -> Bool",
              "(&&) a b = if a then b else False",
              --
              "(||) : Bool -> Bool -> Bool",
              "(||) a b = if a then True else b",
              -- Base comparison function. All other comparison functions are
              -- defined through this function.
              "(<=) : Int -> Int -> Bool",
              --
              "(==) : Int -> Int -> Bool",
              "(==) a b = a <= b && b <= a",
              --
              "(/=) : Int -> Int -> Bool",
              "(/=) a b = not (a == b)",
              --
              "(<) : Int -> Int -> Bool",
              "(<) a b = a <= b && a /= b",
              --
              "(>) : Int -> Int -> Bool",
              "(>) a b = a >= b && a /= b",
              --
              "(>=) : Int -> Int -> Bool",
              "(>=) a b = b <= a",
              --
              "fst : ∀(a:TL). ∀(b:TU). (a, b) -> a",
              "fst ab = let (a, _) = ab in a",
              --
              "snd : ∀(a:TU). ∀(b:TL). (a, b) -> b",
              "snd ab = let (_, b) = ab in b",
              -- Session operations.
              "send : ∀(a : ML). ∀(s : SL). a -> !a.s -o s",
              "receive : ∀(a : ML). ∀(s : SL). ?a.s -> (a, s)",
              -- Arithmetic operations.
              "(+) : Int -> Int -> Int",
              "(-) : Int -> Int -> Int",
              "(*) : Int -> Int -> Int",
              "(/) : Int -> Int -> Int",
              "(%) : Int -> Int -> Int"
            ]
       in parseTH mempty BuiltinsModule B.builtinsPartialModuleMap defs
    )
