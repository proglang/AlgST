{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module AlgST.Syntax.Type
  ( -- * Types
    Type (..),

    -- ** Polarity
    Polarity (..),
    flipPolarity,

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
  )
where

import qualified AlgST.Syntax.Kind as K
import qualified Data.Kind as HS
import Language.Haskell.TH.Syntax (Lift)
import Syntax.Base
import Syntax.TypeVariable (TypeVar)

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

type ForallX (c :: HS.Type -> HS.Constraint) x =
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

data Type x
  = -- | > Unit _                     ~ ()
    Unit (XUnit x)
  | -- | > Arrow _ Un  t₁ t₂          ~ t₁ -> t₂
    --   > Arrow _ Lin t₁ t₂          ~ t₁ -o t₂
    Arrow (XArrow x) !Multiplicity (Type x) (Type x)
  | -- | > Pair _ t₁ t₂               ~ (t₁, t₂)
    Pair (XPair x) (Type x) (Type x)
  | -- | > Session _ In  t s          ~ ?t.s
    --   > Session _ Out t s          ~ !t.s
    Session (XSession x) !Polarity (Type x) (Type x)
  | -- | > End _                      ~ end
    End (XEnd x)
  | -- | > Forall _ (K.Bind _ v k t)  ~ ∀(v:k). t
    Forall (XForall x) (K.Bind (Type x))
  | -- | Var _ v                      ~ v
    Var (XVar x) !TypeVar
  | -- | Con _ c                      ~ c
    Con (XCon x) !TypeVar
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

instance ForallX Position x => Position (Type x) where
  pos (Unit x) = pos x
  pos (Arrow x _ _ _) = pos x
  pos (Pair x _ _) = pos x
  pos (Session x _ _ _) = pos x
  pos (End x) = pos x
  pos (Forall x _) = pos x
  pos (Var x _) = pos x
  pos (Con x _) = pos x
  pos (App x _ _) = pos x
  pos (Negate x _) = pos x
  pos (Dualof x _) = pos x
  pos (Type x) = pos x
