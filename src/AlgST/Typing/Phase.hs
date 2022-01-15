{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

module AlgST.Typing.Phase where

import AlgST.Parse.Unparser
import qualified AlgST.Syntax.Decl as D
import qualified AlgST.Syntax.Expression as E
import qualified AlgST.Syntax.Kind as K
import AlgST.Syntax.Program (Program)
import AlgST.Syntax.Traversal
import AlgST.Syntax.Tree
import qualified AlgST.Syntax.Type as T
import AlgST.Syntax.Variable
import AlgST.Typing.Equality
import Data.Functor.Const
import Data.Functor.Identity
import Data.Void

-- | Typing phase token.
--
-- After typechecking all expressions are annotated with their type, type
-- aliases are expanded and type constructors are represented as 'TypeRef'.
data Tc

instance VarTraversable TcExpX Tc where
  traverseVars proxy = \case
    ValueCase p exp map ->
      ValueCase p
        <$> traverseVars proxy exp
        <*> traverseVars proxy map
    RecvCase p exp map ->
      RecvCase p
        <$> traverseVars proxy exp
        <*> traverseVars proxy map

instance LabeledTree TcExpX where
  labeledTree =
    pure . \case
      RecvCase _ exp map ->
        tree
          "TcExpX.RecvCase"
          [labeledTree exp, fieldMapTree map]
      ValueCase _ exp map ->
        tree
          "TcExpX.ValueCase"
          [labeledTree exp, fieldMapTree map]

instance Position TcExpX where
  pos = \case
    ValueCase p _ _ -> p
    RecvCase p _ _ -> p

data TcExpX
  = -- | > ValueCase _ e cases        ~ case e of { cases... }
    ValueCase !Pos !TcExp !(TcCaseMap [] Maybe)
  | -- | > RecvCase _ e cases         ~ case e of { cases... }
    RecvCase !Pos !TcExp !(TcCaseMap Identity (Const ()))

instance Unparse TcExpX where
  unparse = \case
    ValueCase _ e cm -> unparseCase e cm
    RecvCase _ e cm -> unparseCase e cm

-- | Replaces @"AlgST.Syntax.Type".'T.Con'@/@"AlgST.Syntax.Type".'T.App'@
-- combinations after type checking.
data TypeRef = TypeRef
  { typeRefPos :: Pos,
    typeRefName :: !TypeVar,
    typeRefArgs :: [TcType],
    typeRefKind :: !K.Kind
  }

instance Position TypeRef where
  pos = typeRefPos

instance Equivalence TypeRef where
  alpha w m r1 r2 =
    and $
      (typeRefName r1 == typeRefName r2) :
      -- Given that both 'TypeRef's have the same name they must have the same
      -- number of arguments.
      zipWith (alpha w m) (typeRefArgs r1) (typeRefArgs r2)

instance VarTraversable TypeRef Tc where
  traverseVars proxy ref = do
    name <- constructor proxy (typeRefName ref)
    args <- traverse (traverseVars proxy) (typeRefArgs ref)
    pure
      TypeRef
        { typeRefName = name,
          typeRefArgs = args,
          typeRefKind = typeRefKind ref,
          typeRefPos = typeRefPos ref
        }

instance Unparse TypeRef where
  unparse r = unparseApp (show (typeRefName r)) (typeRefArgs r)

instance LabeledTree TypeRef where
  -- We can't include the whole typeRefDecl since the type graph might be
  -- recursive and the LabeledTree class is not equipped to handle cyclic
  -- structures.
  labeledTree ref =
    pure . Node "TypeRef" $
      leaf (show (typeRefName ref)) :
      concatMap labeledTree (typeRefArgs ref)

-- | Returns the types kind.
--
-- This function does no checking but assumes that the given type is well
-- formed. It does the minmal amount of work to determine the type's kind.
typeKind :: TcType -> K.Kind
typeKind t = case t of
  T.Unit p -> K.MU p
  T.Arrow p m _ _ -> K.Kind p K.Top m
  T.Pair _ t u ->
    K.leastUpperBound (typeKind t) (typeKind u)
  T.Session p _ _ _ -> K.SL p
  T.End p -> K.SU p
  T.Forall p (K.Bind _ _ _ t) ->
    maybe malformed (K.Kind p K.Top) (K.multiplicity (typeKind t))
  T.Var k _ -> k
  T.Con x _ -> absurd x
  T.App x _ _ -> absurd x
  T.Dualof _ t -> typeKind t
  T.Negate p _ -> K.P p
  T.Type r -> typeRefKind r
  where
    malformed = error $ "internal error: malformed type " ++ show t

tcDeclKind :: D.TypeDecl Tc -> K.Kind
tcDeclKind = \case
  D.AliasDecl x _ -> absurd x
  D.DataDecl _ d -> D.nominalKind d
  D.ProtoDecl _ d -> D.nominalKind d

{- ORMOLU_DISABLE -}
type TcExp = E.Exp Tc
type TcType = T.Type Tc
type TcBind = E.Bind Tc
type TcCaseMap f g = E.CaseMap' f g Tc
type TcProgram = Program Tc

type instance E.XLit    Tc = Pos
type instance E.XVar    Tc = Pos
type instance E.XCon    Tc = Pos
type instance E.XAbs    Tc = Pos
type instance E.XApp    Tc = Pos
type instance E.XPair   Tc = Pos
type instance E.XCond   Tc = Void     -- Desugared to @'E.Exp' ('ValueCase' _ _)@.
type instance E.XCase   Tc = Void     -- E.Exp ValueCase / E.Exp RecvCase
type instance E.XTAbs   Tc = Pos
type instance E.XTApp   Tc = Pos
type instance E.XUnLet  Tc = Void     -- Desugared to 'Case'.
type instance E.XPatLet Tc = Void     -- Desugared to 'Case'.
type instance E.XRec    Tc = Pos
type instance E.XNew    Tc = Pos
type instance E.XSelect Tc = Pos
type instance E.XExp    Tc = TcExpX

type instance E.XBind Tc = Pos

type instance T.XUnit    Tc = Pos
type instance T.XArrow   Tc = Pos
type instance T.XPair    Tc = Pos
type instance T.XSession Tc = Pos
type instance T.XEnd     Tc = Pos
type instance T.XForall  Tc = Pos
type instance T.XVar     Tc = K.Kind
type instance T.XCon     Tc = Void  -- Con/App nodes are replaced by TypeRef nodes.
type instance T.XApp     Tc = Void
type instance T.XDualof  Tc = Pos
type instance T.XNegate  Tc = Pos
type instance T.XType    Tc = TypeRef

type instance D.XAliasDecl    Tc = Void  -- Type aliases have been expanded after type checking.
type instance D.XDataDecl     Tc = D.Origin
type instance D.XProtocolDecl Tc = D.Origin

type instance D.XDataCon      Tc = D.Origin
type instance D.XProtoCon     Tc = D.Origin
{- ORMOLU_ENABLE -}
