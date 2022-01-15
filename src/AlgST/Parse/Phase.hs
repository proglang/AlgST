{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module AlgST.Parse.Phase where

import AlgST.Parse.Unparser
import qualified AlgST.Syntax.Decl as D
import qualified AlgST.Syntax.Expression as E
import AlgST.Syntax.Program
import AlgST.Syntax.Traversal
import AlgST.Syntax.Tree
import qualified AlgST.Syntax.Type as T
import Data.Void
import Language.Haskell.TH.Syntax (Lift)
import Syntax.Base

data Parse

newtype BuiltinNew = BuiltinNew Pos
  deriving (Lift)

instance Position BuiltinNew where
  pos (BuiltinNew p) = p

instance Unparse BuiltinNew where
  unparse _ = unparseApp "new" ([] @Void)

instance VarTraversable BuiltinNew Parse where
  -- Builtin is a leaf type, there is nothing to traverse.
  traverseVars _proxy = pure

instance LabeledTree BuiltinNew where
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
type instance E.XNew    Parse = Void
type instance E.XSelect Parse = Pos
type instance E.XExp    Parse = BuiltinNew

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
