{-# LANGUAGE TypeFamilies #-}

module AlgST.Util where

import qualified Data.List as List
import Data.List.NonEmpty (NonEmpty (..))
import Data.Maybe
import Data.Ord
import Syntax.Base (Pos, Position (..))

joinConnector :: String -> NonEmpty String -> ShowS
joinConnector _ (x :| []) =
  showString x
joinConnector c (x :| [y]) =
  showString x . showString ", " . showString c . showChar ' ' . showString y
joinConnector c (x :| y : ys) =
  showString x . showString ", " . joinConnector c (y :| ys)

joinOr :: NonEmpty String -> String
joinOr xs = joinConnector "or" xs ""

joinAnd :: NonEmpty String -> String
joinAnd xs = joinConnector "and" xs ""

whenJust :: Applicative f => Maybe a -> (a -> f ()) -> f ()
whenJust = flip $ maybe (pure ())

-- Like @take n xs@ but adds an extra item in case some elements were
-- discarded.
truncate :: Int -> a -> [a] -> [a]
truncate n a as = zipWith fromMaybe as $ replicate n Nothing ++ [Just a]

class Counted a where
  pluralZ :: (zero ~ b, one ~ b, many ~ b) => a -> zero -> one -> many -> b

{- ORMOLU_DISABLE -}
instance Counted Int where
  pluralZ 0  zero _one _many = zero
  pluralZ 1 _zero  one _many = one
  pluralZ _ _zero _one  many = many

instance Counted [a] where
  pluralZ []   zero _one _many = zero
  pluralZ [_] _zero  one _many = one
  pluralZ _   _zero _one  many = many
{- ORMOLU_ENABLE -}

instance Counted (NonEmpty a) where
  pluralZ (_ :| as) _zero one many = pluralZ as one many many

plural :: (Counted a, one ~ b, many ~ b) => a -> one -> many -> b
plural a one many = pluralZ a many one many

sortPos :: Position a => [a] -> [a]
sortPos =
  -- The @Position@ is usually very easy to access, there is no need for the
  -- decorate-sort-undecorate paradigm used by 'sortOn'.
  List.sortBy (comparing pos)

sortPos' :: [(Pos, a)] -> [(Pos, a)]
sortPos' =
  -- The @Position@ is usually very easy to access, there is no need for the
  -- decorate-sort-undecorate paradigm used by 'sortOn'.
  List.sortBy (comparing fst)
