{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module AlgST.Typing.Equality where

import AlgST.Syntax.Kind qualified as K
import AlgST.Syntax.Name
import AlgST.Syntax.Phases
import AlgST.Syntax.Type qualified as T
import Data.Coerce
import Data.Kind
import Data.Map.Strict qualified as Map
import Data.Void
import GHC.Exts (Proxy#, proxy#)

-- | Use this newtype wrapper to compare two syntax elements with 'Equivalence'
-- instances for alpha equivalence.
type Alpha :: Stage -> Type -> Type
newtype Alpha stage a = Alpha a

instance Equivalence stage a => Eq (Alpha stage a) where
  (==) = coerce (alpha @stage @a proxy# 0 mempty)

class Equivalence stage a where
  -- | Checks for alpha equivalence.
  --
  -- Correctness is only guaranteed if both have been renamed by the same renamer.
  alpha :: Proxy# stage -> Word -> ANameMapG stage Word -> a -> a -> Bool

instance Equivalence stage Void where
  alpha _ _ _ = absurd

instance
  (Equivalence stage (T.XType x), XStage x ~ stage) =>
  Equivalence stage (T.Type x)
  where
  alpha proxy = go
    where
      go !_ _ (T.Unit _) (T.Unit _) =
        True
      go w m (T.Arrow _ s1 m1 t1 u1) (T.Arrow _ s2 m2 t2 u2) =
        and
          [ s1 == s2,
            m1 == m2,
            go w m t1 t2,
            go w m u1 u2
          ]
      go w m (T.Pair _ t1 u1) (T.Pair _ t2 u2) =
        and
          [ go w m t1 t2,
            go w m u1 u2
          ]
      go w m (T.Session _ p1 t1 u1) (T.Session _ p2 t2 u2) =
        and
          [ p1 == p2,
            go w m t1 t2,
            go w m u1 u2
          ]
      go _ _ (T.End _ p1) (T.End _ p2) =
        p1 == p2
      go w m (T.Forall _ (K.Bind _ v1 k1 t1)) (T.Forall _ (K.Bind _ v2 k2 t2)) =
        and
          [ k1 == k2,
            let !m' = Map.insert (liftName v1) w $ Map.insert (liftName v2) w m
             in go (w + 1) m' t1 t2
          ]
      go _ m (T.Var _ v1) (T.Var _ v2) =
        case (Map.lookup (liftName v1) m, Map.lookup (liftName v2) m) of
          (Just x1, Just x2) -> x1 == x2
          (Nothing, Nothing) -> v1 == v2
          _ -> False
      go _ _ (T.Con _ c1) (T.Con _ c2) =
        c1 == c2
      go w m (T.App _ t1 u1) (T.App _ t2 u2) =
        and
          [ go w m t1 t2,
            go w m u1 u2
          ]
      go w m (T.Negate _ t1) (T.Negate _ t2) =
        go w m t1 t2
      go w m (T.Dualof _ t1) (T.Dualof _ t2) =
        go w m t1 t2
      go w m (T.Type x) (T.Type y) =
        alpha proxy w m x y
      go _ _ _ _ =
        False
