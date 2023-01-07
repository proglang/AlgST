module AlgST.Util.PartialOrd where

infix 4 <=?, </=?

class Eq a => PartialOrd a where
  (<=?) :: a -> a -> Bool

-- | Inverse of '(<=?)'.
(</=?) :: PartialOrd a => a -> a -> Bool
a </=? b = not (a <=? b)
