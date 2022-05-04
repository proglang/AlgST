{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Unparsing (turning expressions and types back to their parsable string
-- forms) based on Norman Ramsey, Unparsing Expressions With Prefix and
-- Postfix Operators, Software—Practice and Experience, 1998.
-- https://www.cs.tufts.edu/~nr/pubs/unparse.ps
module AlgST.Parse.Unparser
  ( Unparse (..),
    unparseApp,
    unparseCase,
    showCaseMap,
    showBindType,
  )
where

import AlgST.Syntax.Expression as E
import AlgST.Syntax.Kind qualified as K
import AlgST.Syntax.Name
import AlgST.Syntax.Operators qualified as Op
import AlgST.Syntax.Phases
import AlgST.Syntax.Type qualified as T
import Data.Foldable
import Data.Functor.Identity
import Data.List (intercalate)
import Data.Map.Strict qualified as Map
import Data.Void
import Syntax.Base

instance Show Pos where
  show (Pos l c) = show l ++ ":" ++ show c

instance Show Multiplicity where
  show Un = "U"
  show Lin = "L"

showArrow :: Multiplicity -> String
showArrow Lin = " -o "
showArrow Un = " -> "

showSortedVar :: Show a => Name stage scope -> a -> String
showSortedVar x t = "(" ++ pprName x ++ ":" ++ show t ++ ")"

showKind :: (Show a, Show b) => Name stage scope -> a -> String -> b -> String
showKind var sort arrow term =
  showSortedVar var sort ++ arrow ++ show term

showBindType :: Unparse (T.XType x) => K.Bind (XStage x) (T.Type x) -> String
showBindType (K.Bind _ a k t) = showKind a k ". " t -- ∀ a:k . t

instance (Unparse (E.XExp x), Unparse (T.XType x)) => Show (E.Bind x) where
  show (E.Bind _ m x t e) = showKind x t (showArrow m) e

data Precedence
  = PMin
  | -- | @in@, @else@, @case@, @rec@ (expressions)
    PIn
  | POp Op.Precedence
  | -- | @λ … -> e@ in expressions,  @… -> …@ in types.
    PArrow
  | -- | @T1 . T2@
    PDot
  | -- | @dualof T@
    PDualof
  | -- | @e1 e2@ and @T1 T2@
    PApp
  | PMax
  deriving (Eq, Ord)

type Rator = (Precedence, Op.Associativity)

type Fragment = (Rator, String)

operatorRator :: ProgVar stage -> Maybe Rator
operatorRator op =
  ((,) <$> POp . Op.opPrec <*> Op.opAssoc)
    <$> Map.lookup (nameUnqualified op) Op.knownOperators

minRator, inRator, dotRator, arrowRator, dualofRator, appRator, maxRator :: Rator
inRator = (PIn, Op.R)
dotRator = (PDot, Op.R)
arrowRator = (PArrow, Op.R)
dualofRator = (PDualof, Op.R)
appRator = (PApp, Op.L)
minRator = (PMin, Op.NA)
maxRator = (PMax, Op.NA)

noparens :: Rator -> Rator -> Op.Associativity -> Bool
noparens (pi, ai) (po, ao) side = pi > po || pi == po && ai == ao && ao == side

bracket :: Fragment -> Op.Associativity -> Rator -> String
bracket (inner, image) side outer
  | noparens inner outer side = image
  | otherwise = "(" ++ image ++ ")"

class Unparse t where
  unparse :: t -> Fragment

instance Unparse Void where
  unparse = absurd

unparseApp :: Unparse a => String -> [a] -> Fragment
unparseApp s = go (maxRator, s) . fmap unparse
  where
    go x [] = x
    go x (y : ys) =
      let l = bracket x Op.L appRator
          r = bracket y Op.R appRator
       in go (appRator, l ++ " " ++ r) ys

instance Unparse (T.XType x) => Show (T.Type x) where
  show = snd . unparse

instance Unparse (T.XType x) => Unparse (T.Type x) where
  unparse (T.Unit _) = (maxRator, "()")
  unparse (T.Var _ a) = (maxRator, pprName a)
  unparse (T.Con _ a) = (maxRator, pprName a)
  unparse (T.Session _ p t u) = (dotRator, show p ++ t' ++ "." ++ u')
    where
      t' = bracket (unparse t) Op.L dotRator
      u' = bracket (unparse u) Op.R dotRator
  unparse (T.End _) = (maxRator, "end")
  unparse (T.Arrow _ m t u) = (arrowRator, l ++ showArrow m ++ r)
    where
      l = bracket (unparse t) Op.L arrowRator
      r = bracket (unparse u) Op.R arrowRator
  unparse (T.Pair _ t u) = (maxRator, "(" ++ l ++ ", " ++ r ++ ")")
    where
      l = bracket (unparse t) Op.L minRator
      r = bracket (unparse u) Op.R minRator
  unparse (T.Forall _ b) = (arrowRator, "∀" ++ showBindType b) -- ++ "=>" ++ s)
  unparse (T.Negate _ t) = (dualofRator, "-" ++ s)
    where
      s = bracket (unparse t) Op.R dualofRator
  unparse (T.Dualof _ t) = (dualofRator, "dual " ++ s)
    where
      s = bracket (unparse t) Op.R dualofRator
  unparse (T.App _ a b) = (appRator, l ++ " " ++ r)
    where
      l = bracket (unparse a) Op.L appRator
      r = bracket (unparse b) Op.R appRator
  unparse (T.Type x) = unparse x

instance (Unparse (E.XExp x), Unparse (T.XType x)) => Show (Exp x) where
  show = snd . unparse

instance (Unparse (E.XExp x), Unparse (T.XType x)) => Unparse (Exp x) where
  -- Basic values
  unparse (E.Lit _ l) = unparse l
  unparse (E.Var _ x) = (maxRator, pprName x)
  unparse (E.Con _ x) = (maxRator, pprName x)
  -- Abstraction intro and elim
  unparse (E.Abs _ b) = (arrowRator, "λ" ++ show b)
  unparse (E.App _ (E.App _ (E.Var _ x) e1) e2)
    | Just rator <- operatorRator x =
      let l = bracket (unparse e1) Op.L rator
          r = bracket (unparse e2) Op.R rator
       in (rator, l ++ showOp x ++ r)
  unparse (E.App _ e1 e2) = (appRator, l ++ " " ++ r)
    where
      l = bracket (unparse e1) Op.L appRator
      r = bracket (unparse e2) Op.R appRator
  -- Pair intro and elim
  unparse (E.Pair _ e1 e2) = (maxRator, "(" ++ l ++ ", " ++ r ++ ")")
    where
      l = bracket (unparse e1) Op.L minRator
      r = bracket (unparse e2) Op.R minRator
  -- Datatype elim
  unparse (E.Case _ e m) = unparseCase e m
  -- Type Abstraction intro and elim
  unparse (E.TypeApp _ x t) = (appRator, show x ++ " [" ++ show t ++ "]")
  unparse (E.TypeAbs _ (K.Bind _ a k e)) = (arrowRator, "λ[" ++ showSortedVar a k ++ "] -> " ++ show e)
  -- Boolean elim
  unparse (E.Cond _ e1 e2 e3) =
    (inRator, "if " ++ s1 ++ " then " ++ s2 ++ " else " ++ s3)
    where
      s1 = bracket (unparse e1) Op.L inRator
      s2 = bracket (unparse e2) Op.NA inRator
      s3 = bracket (unparse e3) Op.R inRator
  -- Unary Let
  unparse (E.UnLet _ x Nothing (E.Rec _ x' ty e1) e2)
    | x == x' =
      (inRator, "let rec " ++ pprName x ++ " : " ++ show ty ++ " = " ++ l ++ " in " ++ r)
    where
      l = bracket (unparse (E.RecAbs e1)) Op.L inRator
      r = bracket (unparse e2) Op.R inRator
  unparse (E.UnLet _ x mty e1 e2) =
    (inRator, "let " ++ pprName x ++ annot ++ " = " ++ l ++ " in " ++ r)
    where
      annot = case mty of
        Nothing -> ""
        Just ty -> " : " ++ show ty
      l = bracket (unparse e1) Op.L inRator
      r = bracket (unparse e2) Op.R inRator
  unparse (E.PatLet _ x xs e1 e2) =
    (inRator, unwords s)
    where
      s =
        "let" :
        (pprName . unL <$> defaultPos :@ x : xs)
          ++ ["=", l, "in", r]
      l = bracket (unparse e1) Op.L inRator
      r = bracket (unparse e2) Op.R inRator
  unparse (E.Rec _ x ty r) =
    (inRator, "rec " ++ pprName x ++ " : " ++ show ty ++ " = " ++ show (E.RecAbs r))
  -- Session expressions
  unparse (E.New _ t) = (appRator, "new [" ++ show t ++ "]")
  unparse (E.Select _ (_ :@ con)) = (appRator, "select " ++ pprName con)
  -- Forking
  unparse (E.Fork _ e) = unparseApp "fork" [e]
  unparse (E.Fork_ _ e) = unparseApp "fork_" [e]
  -- Extensions
  unparse (E.Exp x) = unparse x

instance Unparse E.Lit where
  unparse =
    (maxRator,) . \case
      E.Unit -> "()"
      E.Int x -> show x
      E.Char x -> show x
      E.String x -> show x

unparseCase ::
  (Unparse (E.XExp x), Unparse (T.XType x), Foldable f, Foldable g) =>
  E.Exp x ->
  E.CaseMap' f g x ->
  Fragment
unparseCase e m =
  (inRator, "case " ++ s ++ " of {" ++ showCaseMap m ++ "}")
  where
    s = bracket (unparse e) Op.NA inRator

showCaseMap ::
  (Unparse (E.XExp x), Unparse (T.XType x), Foldable f, Foldable g) =>
  CaseMap' f g x ->
  String
showCaseMap m =
  intercalate ", " $
    map showAssoc (Map.toList (casesPatterns m))
      ++ [showWild b | b <- toList (casesWildcard m)]
  where
    showAssoc (c, CaseBranch {branchBinds = binds, branchExp = e}) =
      unwords (pprName . unL <$> defaultPos :@ c : toList binds)
        ++ " -> "
        ++ show e
    showWild CaseBranch {branchBinds = Identity (_ :@ a), branchExp = e} =
      pprName a ++ " -> " ++ show e

showOp :: ProgVar stage -> String
showOp x = " " ++ tail (init $ pprName x) ++ " "
