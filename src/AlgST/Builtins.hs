{-# LANGUAGE TemplateHaskell #-}

module AlgST.Builtins
  ( module AlgST.Builtins.Names,
    builtinsImport,
    builtinsModule,
    builtinsModuleMap,
    builtinsModuleCtxt,
    builtinsEnv,
  )
where

import AlgST.Builtins.Names hiding (builtinsPartialModuleMap)
import AlgST.Builtins.Names qualified as B
import AlgST.Builtins.TH
import AlgST.Rename (ModuleMap, RenameEnv, ResolvedImport)
import AlgST.Rename qualified as Rn
import AlgST.Syntax.Module
import AlgST.Syntax.Name
import AlgST.Syntax.Pos
import AlgST.Typing qualified as Tc
import AlgST.Typing.Phase (TcModule)

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
              "(<&>) : ∀(a:TU). ∀(b:TL). ∀(c:SL). (a, c) -> (a -> b) -o (b, c)",
              "(<&>) x f = let (a, c) = x in (f a, c)",
              -- PT: below type is shady; the type checker does not understand one-branch cases
              "(<*>) : ∀(a:TL). ∀(b:TL). ∀(c1:SL). ∀(c2:SL). ∀(c3:SL). (c1 -o (a -> b, c2)) -> (c2 -> (a, c3)) -o (c1 -o (b, c3))",
              "(<*>) lhs rhs c1 = let (f, c2) = lhs c1 in let (x, c3) = rhs c2 in (f x, c3)",
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
              "sendLin : ∀(a : ML). ∀(s : SL). a -> !a.s -o s",
              "receive : ∀(a : ML). ∀(s : SL). ?a.s -> (a, s)",
              --
              "send : ∀(a : MU). ∀(s : SL). a -> !a.s -> s",
              "send [a] [s] a s = sendLin [a, s] a s",
              -- Arithmetic operations.
              "(+) : Int -> Int -> Int",
              "(-) : Int -> Int -> Int",
              "(*) : Int -> Int -> Int",
              "(/) : Int -> Int -> Int",
              "(%) : Int -> Int -> Int"
            ]
       in parseTH BuiltinsModule B.builtinsPartialModuleMap defs
    )

builtinsImport :: ResolvedImport
builtinsImport =
  Import
    { importTarget = (BuiltinsModule, builtinsModuleMap),
      importQualifier = emptyModuleName,
      importSelection = ImportAll ZeroPos mempty mempty
    }

builtinsEnv :: RenameEnv
builtinsEnv =
  Rn.importAllEnv ZeroPos BuiltinsModule builtinsModuleMap emptyModuleName
