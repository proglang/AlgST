{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module AlgST.Syntax.Type
  ( -- * Types
    Type (..),

    -- ** Annotations
    Polarity (..),
    flipPolarity,
    Specificity (..),
    eitherImplicit,

    -- ** Extension families
    XUnit,
    XArrow,
    XPair,
    XSession,
    XEnd,
    XForall,
    XVar,
    XCon,
    XApp,
    XDualof,
    XNegate,
    XType,
    ForallX,
    SameX,
  )
where

import AlgST.Syntax.Kind qualified as K
import AlgST.Syntax.Phases
import Language.Haskell.TH.Syntax (Lift)

data Polarity
  = -- | @?@
    In
  | -- | @!@
    Out
  deriving (Eq, Lift)

flipPolarity :: Polarity -> Polarity
flipPolarity = \case
  In -> Out
  Out -> In

instance Show Polarity where
  show In = "?"
  show Out = "!"

{- ORMOLU_DISABLE -}
type family XUnit x
type family XArrow x
type family XPair x
type family XSession x
type family XEnd x
type family XForall x
type family XVar x
type family XCon x
type family XApp x
type family XDualof x
type family XNegate x
type family XType x
{- ORMOLU_ENABLE -}

type ForallX :: CAll
type ForallX c x =
  ( c (XUnit x),
    c (XArrow x),
    c (XPair x),
    c (XSession x),
    c (XEnd x),
    c (XForall x),
    c (XVar x),
    c (XCon x),
    c (XApp x),
    c (XDualof x),
    c (XNegate x),
    c (XType x)
  )

type SameX :: CSame
type SameX x y =
  ( XUnit x ~ XUnit y,
    XArrow x ~ XArrow y,
    XPair x ~ XPair y,
    XSession x ~ XSession y,
    XEnd x ~ XEnd y,
    XForall x ~ XForall y,
    XCon x ~ XCon y,
    XApp x ~ XApp y,
    XDualof x ~ XDualof y,
    XNegate x ~ XNegate y
  )

data Specificity
  = Explicit
  | Implicit
  deriving stock (Show, Eq, Lift)

eitherImplicit :: Specificity -> Specificity -> Specificity
eitherImplicit Implicit _ = Implicit
eitherImplicit _ Implicit = Implicit
eitherImplicit _ _ = Explicit

data Type x
  = -- | > Unit _                     ~ ()
    Unit (XUnit x)
  | -- | > Arrow _ Explicit Un  t₁ t₂          ~ t₁ -> t₂
    --   > Arrow _ Explicit Lin t₁ t₂          ~ t₁ -o t₂
    --   > Arrow _ Implicit Un  t₁ t₂          ~ t₁ ?-> t₂
    --   > Arrow _ Implicit Lin t₁ t₂          ~ t₁ ?-o t₂
    Arrow (XArrow x) !Specificity !K.Multiplicity (Type x) (Type x)
  | -- | > Pair _ t₁ t₂               ~ (t₁, t₂)
    Pair (XPair x) (Type x) (Type x)
  | -- | > Session _ In  t s          ~ ?t.s
    --   > Session _ Out t s          ~ !t.s
    Session (XSession x) !Polarity (Type x) (Type x)
  | -- | > End _ In                   ~ End?
    --   > End _ Out                  ~ End!
    End (XEnd x) !Polarity
  | -- | > Forall _ (K.Bind _ v k t)  ~ ∀(v:k). t
    Forall (XForall x) (K.Bind (XStage x) (Type x))
  | -- | Var _ v                      ~ v
    Var (XVar x) !(XTypeVar x)
  | -- | Con _ c                      ~ c
    Con (XCon x) !(XTypeVar x)
  | -- | App _ t₁ t₂                  ~ t₁ t₂
    App (XApp x) (Type x) (Type x)
  | -- | Dualof _ t                   ~ dual t
    Dualof (XDualof x) (Type x)
  | -- | Negate _ t                   ~ -t
    Negate (XNegate x) (Type x)
  | -- | Constructor extension. Depends on the instantiation of the 'XExp' type
    -- family.
    Type (XType x)

deriving stock instance ForallX Lift x => Lift (Type x)

instance ForallX HasPos x => HasPos (Type x) where
  pos (Unit x) = pos x
  pos (Arrow x _ _ _ _) = pos x
  pos (Pair x _ _) = pos x
  pos (Session x _ _ _) = pos x
  pos (End x _) = pos x
  pos (Forall x _) = pos x
  pos (Var x _) = pos x
  pos (Con x _) = pos x
  pos (App x _ _) = pos x
  pos (Negate x _) = pos x
  pos (Dualof x _) = pos x
  pos (Type x) = pos x
