{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module AlgST.Typing.Equality where

import qualified AlgST.Syntax.Kind as K
import qualified AlgST.Syntax.Type as T
import AlgST.Syntax.Variable
import qualified Data.Map.Strict as Map
import Data.Void

class Equivalence a where
  -- | Checks for alpha equivalence.
  --
  -- Correctness is only guaranteed if both have been renamed by the same renamer.
  alpha :: Word -> Map.Map PTVar Word -> a -> a -> Bool

instance Equivalence Void where
  alpha _ _ = absurd

-- | Use this newtype wrapper to compare two syntax elements with 'Equivalence'
-- instances for alpha equivalence.
newtype Alpha a = Alpha a

instance Equivalence a => Eq (Alpha a) where
  Alpha a == Alpha b = alpha 0 mempty a b

instance Equivalence (T.XType x) => Equivalence (T.Type x) where
  alpha = go
    where
      go :: Equivalence (T.XType x) => Word -> Map.Map PTVar Word -> T.Type x -> T.Type x -> Bool
      go !_ _ (T.Unit _) (T.Unit _) =
        True
      go w m (T.Arrow _ m1 t1 u1) (T.Arrow _ m2 t2 u2) =
        and
          [ m1 == m2,
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
      go _ _ (T.End _) (T.End _) =
        True
      go w m (T.Forall _ (K.Bind _ v1 k1 t1)) (T.Forall _ (K.Bind _ v2 k2 t2)) =
        and
          [ k1 == k2,
            let !m' = Map.insert (Right v1) w $ Map.insert (Right v2) w m
             in go (w + 1) m' t1 t2
          ]
      go _ m (T.Var _ v1) (T.Var _ v2) =
        case (Map.lookup (Right v1) m, Map.lookup (Right v2) m) of
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
        alpha w m x y
      go _ _ _ _ =
        False
