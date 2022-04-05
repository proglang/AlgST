{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

module AlgST.Syntax.Expression
  ( -- * Expressions
    Exp (..),
    Lit (..),
    RecLam (..),
    pattern RecAbs,
    CaseMap,
    CaseMap' (..),
    emptyCaseMap,
    CaseBranch (..),
    foldTypeApps,

    -- ** Extension families
    XLit,
    XVar,
    XCon,
    XAbs,
    XApp,
    XPair,
    XCond,
    XCase,
    XTAbs,
    XTApp,
    XUnLet,
    XPatLet,
    XRec,
    XNew,
    XSelect,
    XFork,
    XFork_,
    XExp,
    ForallX,

    -- * Binds
    Bind (..),
    XBind,
  )
where

import AlgST.Syntax.Kind qualified as K
import AlgST.Syntax.Type qualified as T
import Control.Applicative
import Data.Functor.Identity
import Data.Kind qualified as HS
import Data.Map.Strict qualified as Map
import Instances.TH.Lift ()
import Language.Haskell.TH.Syntax (Lift)
import Syntax.Base
import Syntax.ProgramVariable
import Data.Foldable

{- ORMOLU_DISABLE -}
type family XLit x
type family XVar x
type family XCon x
type family XAbs x
type family XApp x
type family XPair x
type family XCond x
type family XCase x
type family XTAbs x
type family XTApp x
type family XRec x
type family XUnLet x
type family XPatLet x
type family XNew x
type family XSelect x
type family XFork x
type family XFork_ x
type family XExp x
{- ORMOLU_ENABLE -}

type ForallX (c :: HS.Type -> HS.Constraint) x =
  ( c (XLit x),
    c (XVar x),
    c (XCon x),
    c (XAbs x),
    c (XApp x),
    c (XPair x),
    c (XCond x),
    c (XCase x),
    c (XTAbs x),
    c (XTApp x),
    c (XRec x),
    c (XUnLet x),
    c (XPatLet x),
    c (XNew x),
    c (XSelect x),
    c (XFork x),
    c (XFork_ x),
    c (XExp x),
    c (XBind x)
  )

data Lit
  = Unit
  | Int !Integer
  | Char !Char
  | String !String
  deriving (Lift)

data Exp x
  = Lit (XLit x) !Lit
  | -- | > Var _ v                    ~ v
    Var (XVar x) !ProgVar
  | -- | > Con _ c                    ~ c
    Con (XCon x) !ProgVar
  | -- | > Abs _ (Bind _ Un  x t e)   ~ \(x:t) -> e
    --   > Abs _ (Bind _ Lin x t e)   ~ \(x:t) -o e
    Abs (XAbs x) (Bind x)
  | -- | > App _ e₁ e₂                ~ e₁ e₂
    App (XApp x) (Exp x) (Exp x)
  | -- | > Pair _ e₁ e₂               ~ (e₁, e₂)
    Pair (XPair x) (Exp x) (Exp x)
  | -- | > Cond _ e₁ e₂ e₃            ~ if e₁ then e₂ else e₃
    Cond (XCond x) (Exp x) (Exp x) (Exp x)
  | -- | > Case _ e c                 ~ case e of { c }
    Case (XCase x) (Exp x) (CaseMap x)
  | -- | > TypeAbs _ (K.Bind _ v k e) ~ \[v:k] -> e
    TypeAbs (XTAbs x) (K.Bind (Exp x))
  | -- | > TypeApp _ e t              ~ e [t]
    TypeApp (XTApp x) (Exp x) (T.Type x)
  | -- | > UnLet _ x Nothing  e₁ e₂   ~ let x     = e₁ in e₂
    --   > UnLet _ x (Just t) e₁ e₂   ~ let x : t = e₁ in e₂
    UnLet (XUnLet x) !ProgVar (Maybe (T.Type x)) (Exp x) (Exp x)
  | -- | > PatLet _ c [x̅] e₁ e₂       ~ let c x̅ = e₁ in e₂
    --
    -- The first 'ProgVar' should be constructor name, the remaining 'ProgVar's
    -- should be variable names or wildcards.
    PatLet (XPatLet x) !ProgVar [ProgVar] (Exp x) (Exp x)
  | -- | > Rec _ x t r                ~ rec x : t = r
    Rec (XRec x) !ProgVar (T.Type x) (RecLam x)
  | -- | > New _ t                    ~ new [t]
    New (XNew x) (T.Type x)
  | -- | > Select _ c                 ~ select c
    Select (XSelect x) !ProgVar
  | -- | > Fork _ e                   ~ fork e
    Fork (XFork x) (Exp x)
  | -- | > Fork_ _ e                  ~ fork_ e
    Fork_ (XFork_ x) (Exp x)
  | -- | Constructor extension. Depends on the instantiation of the 'XExp' type
    -- family.
    Exp (XExp x)

deriving stock instance (ForallX Lift x, T.ForallX Lift x) => Lift (Exp x)

-- | A restricted version of 'Exp' which binds at least one value via lambda
-- abstraction.
data RecLam x
  = RecTermAbs (XAbs x) (Bind x)
  | RecTypeAbs (XTAbs x) (K.Bind (RecLam x))

deriving stock instance (ForallX Lift x, T.ForallX Lift x) => Lift (RecLam x)

-- | Pattern to convert between 'Exp' and 'RecLam'.
--
-- Used as an expression it will embed the more restricted 'RecLam' into an
-- 'Exp. Used as a pattern it tries to extract a valid 'RecLam' value from an
-- 'Exp'.
pattern RecAbs :: RecLam x -> Exp x
pattern RecAbs recLam <-
  (viewRecLam -> Just recLam)
  where
    RecAbs = \case
      RecTermAbs x b -> Abs x b
      RecTypeAbs x (K.Bind p v t r) -> TypeAbs x $ K.Bind p v t $ RecAbs r

viewRecLam :: Exp x -> Maybe (RecLam x)
viewRecLam (Abs x b) =
  Just (RecTermAbs x b)
viewRecLam (TypeAbs x (K.Bind p v t e)) =
  RecTypeAbs x . K.Bind p v t <$> viewRecLam e
viewRecLam _ =
  Nothing

foldTypeApps :: Foldable f => (Exp x -> T.Type x -> XTApp x) -> Exp x -> f (T.Type x) -> Exp x
foldTypeApps f = foldl' \e ty -> TypeApp (f e ty) e ty

type CaseMap x = CaseMap' [] Maybe x

-- | A map from constructor names to 'CaseBranch'es, plus potentially a wildcard
-- branch.
data CaseMap' f g x = CaseMap
  { casesPatterns :: Map.Map ProgVar (CaseBranch f x),
    casesWildcard :: g (CaseBranch Identity x)
  }

deriving stock instance
  (ForallX Lift x, T.ForallX Lift x, Lift (f ProgVar), Lift (g (CaseBranch Identity x))) =>
  Lift (CaseMap' f g x)

emptyCaseMap :: Alternative g => CaseMap' f g x
emptyCaseMap = CaseMap Map.empty empty

data CaseBranch f x = CaseBranch
  { branchPos :: !Pos,
    branchBinds :: !(f ProgVar),
    branchExp :: Exp x
  }

deriving stock instance
  (ForallX Lift x, T.ForallX Lift x, Lift (f ProgVar)) =>
  Lift (CaseBranch f x)

instance Position (CaseBranch f x) where
  pos = branchPos

instance ForallX Position x => Position (Exp x) where
  pos (Lit x _) = pos x
  pos (Var x _) = pos x
  pos (Con x _) = pos x
  pos (Abs x _) = pos x
  pos (UnLet x _ _ _ _) = pos x
  pos (Rec x _ _ _) = pos x
  pos (App x _ _) = pos x
  pos (TypeApp x _ _) = pos x
  pos (TypeAbs x _) = pos x
  pos (Cond x _ _ _) = pos x
  pos (Pair x _ _) = pos x
  pos (PatLet x _ _ _ _) = pos x
  pos (Case x _ _) = pos x
  pos (New x _) = pos x
  pos (Select x _) = pos x
  pos (Fork x _) = pos x
  pos (Fork_ x _) = pos x
  pos (Exp x) = pos x

-- Bind

type family XBind x

data Bind x = Bind (XBind x) !Multiplicity !ProgVar (T.Type x) (Exp x)

deriving stock instance (ForallX Lift x, T.ForallX Lift x) => Lift (Bind x)

instance Position (XBind x) => Position (Bind x) where
  pos (Bind x _ _ _ _) = pos x
