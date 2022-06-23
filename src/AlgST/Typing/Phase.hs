{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

module AlgST.Typing.Phase where

import AlgST.Parse.Unparser
import AlgST.Syntax.Decl qualified as D
import AlgST.Syntax.Expression qualified as E
import AlgST.Syntax.Kind qualified as K
import AlgST.Syntax.Module (Module)
import AlgST.Syntax.Name
import AlgST.Syntax.Phases
import AlgST.Syntax.Traversal
import AlgST.Syntax.Tree
import AlgST.Syntax.Type qualified as T
import AlgST.Typing.Equality
import AlgST.Typing.Subtyping
import Data.Functor.Const
import Data.Functor.Identity
import Data.Void
import Language.Haskell.TH.Syntax (Lift)
import Syntax.Base

-- | Typing phase token.
--
-- After typechecking all expressions are annotated with their type, type
-- aliases are expanded and type constructors are represented as 'TypeRef'.
data Tc

instance SynTraversable TcExpX Tc TcExpX Tc where
  traverseSyntax proxy = \case
    ValueCase p exp map ->
      ValueCase p
        <$> traverseSyntax proxy exp
        <*> traverseSyntax proxy map
    RecvCase p exp map ->
      RecvCase p
        <$> traverseSyntax proxy exp
        <*> traverseSyntax proxy map

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
  deriving stock (Lift)

instance Unparse TcExpX where
  unparse = \case
    ValueCase _ e cm -> unparseCase e cm
    RecvCase _ e cm -> unparseCase e cm

-- | Replaces @"AlgST.Syntax.Type".'T.Con'@/@"AlgST.Syntax.Type".'T.App'@
-- combinations after type checking.
data TypeRef = TypeRef
  { typeRefPos :: Pos,
    typeRefName :: !(TypeVar TcStage),
    typeRefArgs :: [TcType],
    typeRefKind :: !K.Kind
  }
  deriving stock (Lift)

instance Position TypeRef where
  pos = typeRefPos

instance Equivalence TcStage TypeRef where
  alpha proxy w m r1 r2 =
    and $
      (typeRefName r1 == typeRefName r2) :
      -- Given that both 'TypeRef's have the same name they must have the same
      -- number of arguments.
      zipWith (alpha proxy w m) (typeRefArgs r1) (typeRefArgs r2)

instance Subtype TcStage TypeRef where
  beta proxy w m r1 r2 =
    and $
      (typeRefName r1 == typeRefName r2) :
      -- Given that both 'TypeRef's have the same name they must have the same
      -- number of arguments.
      -- deliberately reverting to alpha to enforce invariance!
      zipWith (alpha proxy w m) (typeRefArgs r1) (typeRefArgs r2)

instance SynTraversable TypeRef Tc TypeRef Tc where
  traverseSyntax proxy ref = do
    args <- traverse (traverseSyntax proxy) (typeRefArgs ref)
    pure
      TypeRef
        { -- We are explicit in the fields so that an error is generated if there
          -- are fields added which might require traversing.
          typeRefName = typeRefName ref,
          typeRefArgs = args,
          typeRefKind = typeRefKind ref,
          typeRefPos = typeRefPos ref
        }

instance Unparse TypeRef where
  unparse r = unparseApp (pprName (typeRefName r)) (typeRefArgs r)

instance LabeledTree TypeRef where
  -- We can't include the whole typeRefDecl since the type graph might be
  -- recursive and the LabeledTree class is not equipped to handle cyclic
  -- structures.
  labeledTree ref =
    pure . Node "TypeRef" $
      leaf (pprName (typeRefName ref)) :
      concatMap labeledTree (typeRefArgs ref)

-- | Returns the types kind.
--
-- This function does no checking but assumes that the given type is well
-- formed. It does the minmal amount of work to determine the type's kind.
typeKind :: TcType -> K.Kind
typeKind t = case t of
  T.Unit _ -> K.MU
  T.Arrow _ m _ _ -> K.Kind K.Top m
  T.Pair _ t u ->
    K.leastUpperBound (typeKind t) (typeKind u)
  T.Session {} -> K.SL
  T.End _ -> K.SU
  T.Forall _ (K.Bind _ _ _ t) ->
    maybe malformed (K.Kind K.Top) (K.multiplicity (typeKind t))
  T.Var k _ -> unL k
  T.Con x _ -> absurd x
  T.App x _ _ -> absurd x
  T.Dualof _ t -> typeKind t
  T.Negate _ _ -> K.P
  T.Type r -> typeRefKind r
  where
    malformed = error $ "internal error: malformed type " ++ show t

tcDeclKind :: D.TypeDecl Tc -> K.Kind
tcDeclKind = \case
  D.AliasDecl x _ -> absurd x
  D.DataDecl _ d -> D.nominalKind d
  D.ProtoDecl _ d -> D.nominalKind d

{- ORMOLU_DISABLE -}
type TcName                = XName Tc
type TcExp                 = E.Exp Tc
type TcType                = T.Type Tc
type TcBind                = E.Bind Tc
type TcCaseMap f g         = E.CaseMap' f g Tc
type TcModule             = Module Tc

type TcStage               = Resolved
type TcNameMap scope       = NameMapG TcStage scope
type TcNameSet scope       = NameSetG TcStage scope
type instance XStage    Tc = TcStage

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
type instance E.XFork   Tc = Pos      -- TODO: Could be desugared to 'New' + 'Fork_' + ...
type instance E.XFork_  Tc = Pos
type instance E.XExp    Tc = TcExpX
type instance E.XBind   Tc = Pos

type instance T.XUnit    Tc = Pos
type instance T.XArrow   Tc = Pos
type instance T.XPair    Tc = Pos
type instance T.XSession Tc = Pos
type instance T.XEnd     Tc = Pos
type instance T.XForall  Tc = Pos
type instance T.XVar     Tc = Located K.Kind
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
