{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StandaloneKindSignatures #-}
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
    XImp,
    XCon,
    XAbs,
    XApp,
    XIApp,
    XPair,
    XCond,
    XCase,
    XTAbs,
    XTApp,
    XUnLet,
    XILet,
    XPatLet,
    XRec,
    XSig,
    XNew,
    XSelect,
    XFork,
    XFork_,
    XExp,
    ForallX,

    -- * Binds
    Bind (..),
    XBind,
    SameX,
  )
where

import AlgST.Syntax.Kind qualified as K
import AlgST.Syntax.Name
import AlgST.Syntax.Phases
import AlgST.Syntax.Type qualified as T
import Control.Applicative
import Data.Foldable
import Data.Functor.Identity
import Instances.TH.Lift ()
import Language.Haskell.TH.Syntax (Lift)

{- ORMOLU_DISABLE -}
type family XLit x
type family XVar x
type family XImp x
type family XCon x
type family XAbs x
type family XApp x
type family XIApp x
type family XPair x
type family XCond x
type family XCase x
type family XTAbs x
type family XTApp x
type family XRec x
type family XSig x
type family XUnLet x
type family XILet x
type family XPatLet x
type family XNew x
type family XSelect x
type family XFork x
type family XFork_ x
type family XExp x
{- ORMOLU_ENABLE -}

type ForallX :: CAll
type ForallX c x =
  ( c (XLit x),
    c (XVar x),
    c (XImp x),
    c (XCon x),
    c (XAbs x),
    c (XApp x),
    c (XIApp x),
    c (XPair x),
    c (XCond x),
    c (XCase x),
    c (XTAbs x),
    c (XTApp x),
    c (XRec x),
    c (XSig x),
    c (XUnLet x),
    c (XILet x),
    c (XPatLet x),
    c (XNew x),
    c (XSelect x),
    c (XFork x),
    c (XFork_ x),
    c (XExp x),
    c (XBind x)
  )

type SameX :: CSame
type SameX x y =
  ( XLit x ~ XLit y,
    XImp x ~ XImp y,
    XCon x ~ XCon y,
    XAbs x ~ XAbs y,
    XApp x ~ XApp y,
    XIApp x ~ XIApp y,
    XPair x ~ XPair y,
    XCond x ~ XCond y,
    XCase x ~ XCase y,
    XTAbs x ~ XTAbs y,
    XTApp x ~ XTApp y,
    XRec x ~ XRec y,
    XSig x ~ XSig y,
    XUnLet x ~ XUnLet y,
    XILet x ~ XILet y,
    XPatLet x ~ XPatLet y,
    XNew x ~ XNew y,
    XSelect x ~ XSelect y,
    XFork x ~ XFork y,
    XFork_ x ~ XFork_ y,
    XBind x ~ XBind y
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
    Var (XVar x) !(XProgVar x)
  | -- | > Imp x                      ~ _
    --
    -- Explicitly resolve an implicit.
    Imp (XImp x)
  | -- | > Con _ c                    ~ c
    Con (XCon x) !(XProgVar x)
  | -- | > Abs _ (Bind _ Un  x t e)   ~ \(x:t) -> e
    --   > Abs _ (Bind _ Lin x t e)   ~ \(x:t) -o e
    Abs (XAbs x) (Bind x)
  | -- | > App _ e₁ e₂                ~ e₁ e₂
    App (XApp x) (Exp x) (Exp x)
  | -- | > IApp _ e₁ e₂               ~ e₁ {e₂}
    IApp (XIApp x) (Exp x) (Exp x)
  | -- | > Pair _ e₁ e₂               ~ (e₁, e₂)
    Pair (XPair x) (Exp x) (Exp x)
  | -- | > Cond _ e₁ e₂ e₃            ~ if e₁ then e₂ else e₃
    Cond (XCond x) (Exp x) (Exp x) (Exp x)
  | -- | > Case _ e c                 ~ case e of { c }
    Case (XCase x) (Exp x) (CaseMap x)
  | -- | > TypeAbs _ (K.Bind _ v k e) ~ \[v:k] -> e
    TypeAbs (XTAbs x) (K.Bind (XStage x) (Exp x))
  | -- | > TypeApp _ e t              ~ e [t]
    TypeApp (XTApp x) (Exp x) (T.Type x)
  | -- | > UnLet _ x Nothing  e₁ e₂   ~ let x     = e₁ in e₂
    --   > UnLet _ x (Just t) e₁ e₂   ~ let x : t = e₁ in e₂
    UnLet (XUnLet x) !(XProgVar x) (Maybe (T.Type x)) (Exp x) (Exp x)
  | -- | “implicit let”
    --
    -- > ILet _ (Just x) (Just t) e₁ e₂   ~ let ?x     = e₁ in e₂
    -- > ILet _ (Just x) Nothing  e₁ e₂   ~ let ?x : t = e₁ in e₂
    -- > ILet _ (Just x) (Just t) e₁ e₂   ~ let ?      = e₁ in e₂
    -- > ILet _ (Just x) (Just t) e₁ e₂   ~ let ?  : t = e₁ in e₂
    --
    -- TODO: When introducing a richer pattern syntax turn @ILet@s into a kind
    -- of pattern.
    ILet (XILet x) !(Maybe (XProgVar x)) !(Maybe (T.Type x)) (Exp x) (Exp x)
  | -- | > PatLet _ c [x̅] e₁ e₂       ~ let c x̅ = e₁ in e₂
    --
    -- The first 'ProgVar' should be the constructor name, the remaining
    -- 'ProgVar's should be variable names or wildcards.
    PatLet (XPatLet x) !(Located (XProgVar x)) [Located (XProgVar x)] (Exp x) (Exp x)
  | -- | > Rec _ x t r                ~ rec x : t = r
    Rec (XRec x) !(XProgVar x) (T.Type x) (RecLam x)
  | -- | > Sig _ e t                  ~ e : t
    Sig (XSig x) (Exp x) (T.Type x)
  | -- | > New _ t                    ~ new [t]
    New (XNew x) (T.Type x)
  | -- | > Select _ c                 ~ select c
    Select (XSelect x) !(Located (XProgVar x))
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
  | RecTypeAbs (XTAbs x) (K.Bind (XStage x) (RecLam x))

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
  { casesPatterns :: NameMapG (XStage x) Values (CaseBranch f x),
    casesWildcard :: g (CaseBranch Identity x)
  }

deriving stock instance
  ( ForallX Lift x,
    T.ForallX Lift x,
    forall a. Lift a => Lift (f a),
    forall a. Lift a => Lift (g a)
  ) =>
  Lift (CaseMap' f g x)

emptyCaseMap :: Alternative g => CaseMap' f g x
emptyCaseMap = CaseMap mempty empty

data CaseBranch f x = CaseBranch
  { branchPos :: Pos,
    branchBinds :: f (Located (XProgVar x)),
    branchExp :: Exp x
  }

deriving stock instance
  (ForallX Lift x, T.ForallX Lift x, forall a. Lift a => Lift (f a)) =>
  Lift (CaseBranch f x)

instance HasPos (CaseBranch f x) where
  pos = branchPos

instance ForallX HasPos x => HasPos (Exp x) where
  pos (Lit x _) = pos x
  pos (Var x _) = pos x
  pos (Imp x) = pos x
  pos (Con x _) = pos x
  pos (Abs x _) = pos x
  pos (UnLet x _ _ _ _) = pos x
  pos (ILet x _ _ _ _) = pos x
  pos (Rec x _ _ _) = pos x
  pos (Sig x _ _) = pos x
  pos (App x _ _) = pos x
  pos (IApp x _ _) = pos x
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

data Bind x
  = Bind (XBind x) !K.Multiplicity !(XProgVar x) (Maybe (T.Type x)) (Exp x)

deriving stock instance (ForallX Lift x, T.ForallX Lift x) => Lift (Bind x)

instance HasPos (XBind x) => HasPos (Bind x) where
  pos (Bind x _ _ _ _) = pos x
