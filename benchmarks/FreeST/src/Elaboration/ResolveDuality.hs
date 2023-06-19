{-# LANGUAGE TupleSections, FlexibleInstances #-}
module Elaboration.ResolveDuality
  ( ResolveDuality(..)
  )
where


import           Elaboration.Duality
import           Syntax.Base
import           Syntax.Expression as E
import qualified Syntax.Kind as K
import           Syntax.Program
import qualified Syntax.Type as T
import           Util.Error
import           Util.FreestState
import           Validation.Substitution

import           Data.Functor
import qualified Data.Set as Set

-- | Resolving the dualof operator

class ResolveDuality t where
   resolve :: t -> FreestState t

instance ResolveDuality TypeEnv where
  resolve = tMapM (\(k, t) -> (k, ) <$> solveType Set.empty t)

instance ResolveDuality VarEnv where
  resolve = tMapM (solveType Set.empty)

instance ResolveDuality ParseEnv where
  resolve = tMapM (\(as, e) -> (as, ) <$> resolve e)

instance ResolveDuality E.Exp where
  resolve (E.Abs p m b         ) = E.Abs p m <$> resolve b
  resolve (E.App  p e1 e2      ) = E.App p <$> resolve e1 <*> resolve e2
  resolve (E.Pair p e1 e2      ) = E.Pair p <$> resolve e1 <*> resolve e2
  resolve (E.BinLet p x y e1 e2) = E.BinLet p x y <$> resolve e1 <*> resolve e2
  resolve (E.Case p e m        ) = E.Case p <$> resolve e <*> resolveFieldMap m
  resolve (E.TypeApp p e t  ) = E.TypeApp p <$> resolve e <*> resolve t
  resolve (E.TypeAbs p b    ) = E.TypeAbs p <$> resolve b
  resolve (E.UnLet p x e1 e2) = E.UnLet p x <$> resolve e1 <*> resolve e2
  resolve e                   = return e

-- This should be an instance but it overlaps with that one of ParseEnv
resolveFieldMap :: FieldMap -> FreestState FieldMap
resolveFieldMap = mapM (\(xs, e) -> (xs, ) <$> resolve e)

instance (ResolveDuality a, ResolveDuality b) => ResolveDuality (Bind a b) where
  resolve (Bind p a t e) = Bind p a <$> resolve t <*> resolve e

-- We need this one, to have the previous one working. In case E.TAbs a is a Kind 
instance ResolveDuality K.Kind where
  resolve = pure

instance ResolveDuality T.Type where
  resolve = solveType Set.empty

type Visited = Set.Set Variable

solveType :: Visited -> T.Type -> FreestState T.Type
-- Functional Types
solveType v (T.Arrow p pol t u) =
  T.Arrow p pol <$> solveType v t <*> solveType v u
solveType v (T.Labelled p s m   ) = T.Labelled p s <$> tMapM (solveType v) m
-- Session Types
solveType v (T.Semi    p t   u) = T.Semi p <$> solveType v t <*> solveType v u
solveType v (T.Message p pol t) = T.Message p pol <$> solveType v t
-- Polymorphism and recursive types
solveType v (T.Forall p (Bind p' a k t)) =
  T.Forall p . Bind p' a k <$> solveType v t
solveType v (  T.Rec    p b) = T.Rec p <$> solveBind solveType v b
-- Dualof
solveType v d@(T.Dualof p t) = addDualof d >> solveDual v (changePos p t)

-- Var, Int, Char, Bool, Unit, Skip, End
solveType _ t                = pure t

solveDual :: Visited -> T.Type -> FreestState T.Type
-- Session Types
solveDual _ t@T.Skip{}          = pure t
solveDual _ t@T.End{}           = pure t
solveDual v (T.Semi    p t   u) = T.Semi p <$> solveDual v t <*> solveDual v u
solveDual v (T.Message p pol t) = T.Message p (dualof pol) <$> solveType v t
solveDual v (T.Labelled p (T.Choice pol) m) =
  T.Labelled p (T.Choice $ dualof pol) <$> tMapM (solveDual v) m
-- Recursive types
solveDual v t@(T.Rec p b) = do
  u <- solveDBind solveDual v b
  return $ cosubs t (var b) (T.Rec p u)
solveDual _ (T.Var p a) = pure $ T.Dualof p $ T.Var p a
-- Dualof
solveDual _ (T.Dualof _ (T.Var p a)) = pure $ T.Var p a
solveDual v d@(T.Dualof p t) = do
--  debugM $ "double dual -> " ++ show d

  addDualof d >> solveType v (changePos p t)
-- Non session-types
solveDual _ t = addError (DualOfNonSession (getSpan t) t) $> t

solveBind
  :: (Visited -> T.Type -> FreestState T.Type)
  -> Visited
  -> Bind a T.Type
  -> FreestState (Bind a T.Type)
solveBind solve v (Bind p a k t) = Bind p a k <$> solve (Set.insert a v) t

solveDBind
  :: (Visited -> T.Type -> FreestState T.Type)
  -> Visited
  -> Bind a T.Type
  -> FreestState (Bind a T.Type)
solveDBind solve v (Bind p a k t) =
  Bind p a k <$> solve (Set.insert a v) (subs (T.Dualof p $ T.Var p a) a t)

-- |Change position of a given type with a given position
changePos :: Span -> T.Type -> T.Type
changePos p (T.Int    _       ) = T.Int p
changePos p (T.Char   _       ) = T.Char p
changePos p (T.String _       ) = T.String p
changePos p (T.Arrow _ pol t u) = T.Arrow p pol t u
changePos p (T.Labelled _ s m  ) = T.Labelled p s m
changePos p (T.Skip _         ) = T.Skip p
changePos p (T.End  _         ) = T.End p
changePos p (T.Semi    _ t   u) = T.Semi p t u
changePos p (T.Message _ pol b) = T.Message p pol b
changePos p (T.Rec    _ xs    ) = T.Rec p xs
changePos p (T.Forall _ xs    ) = T.Forall p xs
changePos p (T.Var    _ x     ) = T.Var p x
changePos p (T.Dualof _ (T.Var _ x)) = T.Dualof p $ T.Var p x
changePos p (T.Dualof _ t     ) = T.Dualof p t
