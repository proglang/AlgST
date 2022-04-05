{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module AlgST.Parse.Phase where

import AlgST.Parse.Unparser
import AlgST.Syntax.Decl qualified as D
import AlgST.Syntax.Expression qualified as E
import AlgST.Syntax.Program
import AlgST.Syntax.Traversal
import AlgST.Syntax.Tree
import AlgST.Syntax.Type qualified as T
import Data.Void
import Language.Haskell.TH.Syntax (Lift)
import Syntax.Base

data Parse

data ParsedBuiltin
  = BuiltinNew Pos
  | BuiltinFork Pos
  | BuiltinFork_ Pos
  deriving (Lift)

instance Position ParsedBuiltin where
  pos (BuiltinNew p) = p
  pos (BuiltinFork p) = p
  pos (BuiltinFork_ p) = p

instance Unparse ParsedBuiltin where
  unparse b = unparseApp x ([] @Void)
    where
      x = case b of
        BuiltinNew _ -> "new"
        BuiltinFork _ -> "fork"
        BuiltinFork_ _ -> "fork_"

instance VarTraversable ParsedBuiltin Parse where
  -- Builtin is a leaf type, there is nothing to traverse.
  traverseVars _proxy = pure

instance LabeledTree ParsedBuiltin where
  labeledTree _ = [leaf "BuiltinNew"]

{- ORMOLU_DISABLE -}
type PExp = E.Exp Parse
type PBind = E.Bind Parse
type PType = T.Type Parse
type PCaseMap = E.CaseMap Parse
type PProgram = Program Parse
type PTypesMap = TypesMap Parse
type PValuesMap = ValuesMap Parse

type instance E.XLit    Parse = Pos
type instance E.XVar    Parse = Pos
type instance E.XCon    Parse = Pos
type instance E.XAbs    Parse = Pos
type instance E.XApp    Parse = Pos
type instance E.XPair   Parse = Pos
type instance E.XCond   Parse = Pos
type instance E.XCase   Parse = Pos
type instance E.XTAbs   Parse = Pos
type instance E.XTApp   Parse = Pos
type instance E.XUnLet  Parse = Pos
type instance E.XPatLet Parse = Pos
type instance E.XRec    Parse = Pos
type instance E.XNew    Parse = Void  -- BuiltinNew
type instance E.XSelect Parse = Pos
type instance E.XFork   Parse = Void  -- BuiltinFork
type instance E.XFork_  Parse = Void  -- BuiltinFork_
type instance E.XExp    Parse = ParsedBuiltin

type instance E.XBind Parse = Pos

type instance T.XUnit    Parse = Pos
type instance T.XArrow   Parse = Pos
type instance T.XPair    Parse = Pos
type instance T.XSession Parse = Pos
type instance T.XEnd     Parse = Pos
type instance T.XForall  Parse = Pos
type instance T.XVar     Parse = Pos
type instance T.XCon     Parse = Pos
type instance T.XApp     Parse = Pos
type instance T.XDualof  Parse = Pos
type instance T.XNegate  Parse = Pos
type instance T.XType    Parse = Void

type instance D.XAliasDecl    Parse = D.Origin
type instance D.XDataDecl     Parse = D.Origin
type instance D.XProtocolDecl Parse = D.Origin

type instance D.XDataCon      Parse = D.Origin
type instance D.XProtoCon     Parse = D.Origin
{- ORMOLU_ENABLE -}
