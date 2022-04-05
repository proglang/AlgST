{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

-- | This module defines an extensible way to traverse the variables in syntax
-- constructs. It is based upon the ideas described in
-- [Writing efficient free variable traversals](https://www.haskell.org/ghc/blog/20190728-free-variable-traversals.html).
module AlgST.Syntax.Traversal
  ( -- * Classes
    VarTraversal (..),
    VarTraversable (..),
    bindOne,

    -- * Predefined Traversals

    -- ** @CollectFree@
    CollectFree (..),
    collectFree,

    -- ** @Any@
    Any (..),
    anyFree,

    -- ** Subsitution
    substituteType,
    substituteTerm,

    -- *** Keeping substitutions around.
    Substitutions (..),
    applySubstitutions,
    nullSubstitutions,
    emptySubstitutions,
    typeSubstitions,
    termSubstitions,

    -- * Traversal helpers
    Two (..),
  )
where

import AlgST.Syntax.Expression qualified as E
import AlgST.Syntax.Kind qualified as K
import AlgST.Syntax.Type qualified as T
import AlgST.Syntax.Variable
import Control.Applicative
import Control.Category ((>>>))
import Control.Monad.Eta
import Control.Monad.Trans.Reader
import Data.Bitraversable
import Data.Foldable
import Data.Functor.Classes
import Data.Functor.Identity
import Data.Map.Strict qualified as Map
import Data.Monoid qualified as M
import Data.Proxy
import Data.Set qualified as Set
import Data.Void

class Applicative f => VarTraversal f x where
  programVariable :: ProgVar -> f (Either (E.Exp x) ProgVar)
  typeVariable :: TypeVar -> f (Either (T.Type x) TypeVar)

  -- | Binds a set of variables for the given computation.
  bind :: (Traversable t, Variable v) => proxy x -> t v -> (t v -> f a) -> f a

bindOne ::
  forall x f v proxy a. (VarTraversal f x, Variable v) => proxy x -> v -> (v -> f a) -> f a
bindOne proxy v f = bind proxy (Identity v) (f . runIdentity)

newtype CollectFree = CollectFree
  { runCollect ::
      -- Bound variables
      Set.Set PTVar ->
      -- Accumulator
      Set.Set PTVar ->
      -- Result
      Set.Set PTVar
  }
  deriving (Monoid) via (Set.Set PTVar -> M.Endo (Set.Set PTVar))

instance Semigroup CollectFree where
  fv1 <> fv2 = CollectFree $ oneShot \bound -> oneShot \acc ->
    runCollect fv1 bound (runCollect fv2 bound acc)

instance VarTraversal (Const CollectFree) x where
  typeVariable = varCollectFree
  programVariable = varCollectFree

  bind _ vs f = Const . CollectFree $ oneShot \bound -> oneShot \acc ->
    let bound' = foldl' (\b v -> Set.insert (liftVar v) b) bound vs
     in runCollect (getConst $ f vs) bound' acc

-- Inserts the given variable into the set of free variables.
varCollectFree :: Variable v => v -> Const CollectFree b
varCollectFree (liftVar -> v) = Const . CollectFree $ oneShot \bound -> oneShot \acc ->
  -- Don't include it if it is either bound or already recorded.
  if v `Set.member` bound || v `Set.member` acc
    then acc
    else Set.insert v acc

-- | Collects all free variables.
collectFree :: forall s x. VarTraversable (s x) x => s x -> Set.Set PTVar
collectFree a = runCollect (getConst (traverseVars @_ @x Proxy a)) mempty mempty

newtype Any = Any {runAny :: Set.Set PTVar -> Bool}
  deriving (Monoid) via (Set.Set PTVar -> M.Any)

instance Semigroup Any where
  fv1 <> fv2 = Any $ oneShot \intresting ->
    runAny fv1 intresting || runAny fv2 intresting

instance VarTraversal (Const Any) x where
  programVariable = anyVariable
  typeVariable = anyVariable

  -- When a variable is bound it will be removed from the set of intresting
  -- variables. If the set becomes empty we will short-circuit to False.
  bind _ vs f = Const . Any $ oneShot \intresting -> do
    let intresting' = foldl' (flip (Set.delete . liftVar)) intresting vs
     in not (Set.null intresting') && runAny (getConst (f vs)) intresting'

anyVariable :: Variable v => v -> Const Any b
anyVariable = Const . Any . Set.member . liftVar

-- | Checks if any of the variables in the given set are free in the given
-- piece of syntax.
anyFree :: forall s x. VarTraversable (s x) x => Set.Set PTVar -> s x -> Bool
anyFree vars a
  | Set.null vars = False
  | otherwise = runAny (getConst (traverseVars @_ @x Proxy a)) vars

data Substitutions x = Substitutions
  { progVarSubs :: !(Map.Map ProgVar (E.Exp x)),
    typeVarSubs :: !(Map.Map TypeVar (T.Type x))
  }

instance
  (VarTraversable (E.XExp x) x, VarTraversable (T.XType x) x) =>
  VarTraversable (Substitutions x) x
  where
  traverseVars proxy subs =
    Substitutions
      <$> traverse (traverseVars proxy) (progVarSubs subs)
      <*> traverse (traverseVars proxy) (typeVarSubs subs)

emptySubstitutions :: Substitutions x
emptySubstitutions = Substitutions Map.empty Map.empty

nullSubstitutions :: Substitutions x -> Bool
nullSubstitutions = (&&) <$> Map.null . progVarSubs <*> Map.null . typeVarSubs

typeSubstitions :: Map.Map TypeVar (T.Type x) -> Substitutions x
typeSubstitions s = emptySubstitutions {typeVarSubs = s}

termSubstitions :: Map.Map ProgVar (E.Exp x) -> Substitutions x
termSubstitions s = emptySubstitutions {progVarSubs = s}

instance Monad m => VarTraversal (ReaderT (Substitutions x) m) x where
  programVariable = etaReaderT . asks . subVar progVarSubs
  typeVariable = etaReaderT . asks . subVar typeVarSubs

  -- Remove the bound variables from the maps.
  bind _ vs f = etaReaderT do
    let removeVar subs =
          liftVar >>> \case
            Left pv -> subs {progVarSubs = Map.delete pv (progVarSubs subs)}
            Right tv -> subs {typeVarSubs = Map.delete tv (typeVarSubs subs)}
    local (\s -> foldl' removeVar s vs) do
      f vs

subVar :: Variable v => (Substitutions x -> Map.Map v a) -> v -> Substitutions x -> Either a v
subVar f v = maybe (Right v) Left . Map.lookup v . f

applySubstitutions :: forall a x. VarTraversable a x => Substitutions x -> a -> a
applySubstitutions s a
  | nullSubstitutions s = a
  | otherwise = runReader (traverseVars (Proxy @x) a) s

-- | Substitute a single 'TypeVar'.
substituteType :: VarTraversable a x => Map.Map TypeVar (T.Type x) -> a -> a
substituteType = applySubstitutions . typeSubstitions

-- | Substitute a single 'ProgVar'.
substituteTerm :: VarTraversable a x => Map.Map ProgVar (E.Exp x) -> a -> a
substituteTerm = applySubstitutions . termSubstitions

newtype Two a = Two {getTwo :: (a, a)}
  deriving stock (Functor, Foldable, Traversable)

instance Applicative Two where
  pure a = Two (a, a)
  Two (fa, fb) <*> Two (a, b) = Two (fa a, fb b)

instance Show1 Two where
  liftShowsPrec f g p (Two xy) =
    showParen (p > 10) $
      liftShowsPrec2 f g f g 11 xy

instance Show a => Show (Two a) where
  showsPrec = showsPrec1

class VarTraversable a x where
  traverseVars :: VarTraversal f x => proxy x -> a -> f a

instance VarTraversable Void x where
  traverseVars _ = absurd

instance (VarTraversable a x, VarTraversable b x) => VarTraversable (Either a b) x where
  traverseVars proxy = bitraverse (traverseVars proxy) (traverseVars proxy)

instance
  (VarTraversable (E.XExp x) x, VarTraversable (T.XType x) x) =>
  VarTraversable (E.Exp x) x
  where
  traverseVars proxy = \case
    e@E.Lit {} ->
      pure e
    E.Var x v ->
      either id (E.Var x)
        <$> programVariable v
    E.Con x v ->
      pure (E.Con x v)
    E.Abs x b ->
      E.Abs x
        <$> traverseVars proxy b
    E.App x e1 e2 ->
      E.App x
        <$> traverseVars proxy e1
        <*> traverseVars proxy e2
    E.Pair x e1 e2 ->
      E.Pair x
        <$> traverseVars proxy e1
        <*> traverseVars proxy e2
    E.UnLet x v mty e k -> do
      let unLet mty' e' (v', k') =
            E.UnLet x v' mty' e' k'
      unLet
        <$> traverse (traverseVars proxy) mty
        <*> traverseVars proxy e
        <*> bindOne proxy v \v' -> (v',) <$> traverseVars proxy k
    E.PatLet x v vs e k -> do
      let patLet e' (vs', k') =
            E.PatLet x v vs' e' k'
      patLet
        <$> traverseVars proxy e
        <*> bind proxy vs \vs' -> (vs',) <$> traverseVars proxy k
    E.Rec x v ty e -> do
      let expRec ty' (v', e') =
            E.Rec x v' ty' e'
      expRec
        <$> traverseVars proxy ty
        <*> bindOne proxy v \v' -> (v',) <$> traverseVars proxy e
    E.Cond x eCond eThen eElse ->
      E.Cond x
        <$> traverseVars proxy eCond
        <*> traverseVars proxy eThen
        <*> traverseVars proxy eElse
    E.Case x e cases ->
      E.Case x
        <$> traverseVars proxy e
        <*> traverseVars proxy cases
    E.TypeAbs x b ->
      E.TypeAbs x
        <$> traverseVars proxy b
    E.TypeApp x e t ->
      E.TypeApp x
        <$> traverseVars proxy e
        <*> traverseVars proxy t
    E.New x t ->
      E.New x
        <$> traverseVars proxy t
    E.Select x c ->
      pure (E.Select x c)
    E.Fork x e ->
      E.Fork x
        <$> traverseVars proxy e
    E.Fork_ x e ->
      E.Fork_ x
        <$> traverseVars proxy e
    E.Exp x ->
      E.Exp
        <$> traverseVars proxy x

instance
  (VarTraversable (E.XExp x) x, VarTraversable (T.XType x) x) =>
  VarTraversable (E.RecLam x) x
  where
  traverseVars proxy = \case
    E.RecTermAbs x b -> E.RecTermAbs x <$> traverseVars proxy b
    E.RecTypeAbs x b -> E.RecTypeAbs x <$> traverseVars proxy b

instance
  (VarTraversable (E.XExp x) x, VarTraversable (T.XType x) x, Traversable f, Traversable g) =>
  VarTraversable (E.CaseMap' f g x) x
  where
  traverseVars proxy cm =
    E.CaseMap
      <$> traverse (traverseVars proxy) (E.casesPatterns cm)
      <*> traverse (traverseVars proxy) (E.casesWildcard cm)

instance
  (VarTraversable (E.XExp x) x, VarTraversable (T.XType x) x, Traversable f) =>
  VarTraversable (E.CaseBranch f x) x
  where
  traverseVars proxy b = bind proxy (E.branchBinds b) \binds -> do
    e <- traverseVars proxy (E.branchExp b)
    pure
      b
        { E.branchBinds = binds,
          E.branchExp = e
        }

instance
  (VarTraversable (E.XExp x) x, VarTraversable (T.XType x) x) =>
  VarTraversable (E.Bind x) x
  where
  traverseVars proxy (E.Bind x m v t e) = do
    let mkBind t' (v', e') =
          E.Bind x m v' t' e'
    mkBind
      <$> traverseVars proxy t
      <*> bindOne proxy v (\v' -> (v',) <$> traverseVars proxy e)

instance VarTraversable (T.XType x) x => VarTraversable (T.Type x) x where
  traverseVars proxy = \case
    t@T.Unit {} ->
      pure t
    T.Arrow x m t u ->
      T.Arrow x m
        <$> traverseVars proxy t
        <*> traverseVars proxy u
    T.Pair x t u ->
      T.Pair x
        <$> traverseVars proxy t
        <*> traverseVars proxy u
    T.Session x p t u ->
      T.Session x p
        <$> traverseVars proxy t
        <*> traverseVars proxy u
    t@T.End {} ->
      pure t
    T.Forall x b ->
      T.Forall x
        <$> traverseVars proxy b
    T.Var x v ->
      either id (T.Var x)
        <$> typeVariable v
    T.Con x v ->
      pure (T.Con x v)
    T.App x t u ->
      T.App x
        <$> traverseVars proxy t
        <*> traverseVars proxy u
    T.Dualof x t ->
      T.Dualof x
        <$> traverseVars proxy t
    T.Negate x t ->
      T.Negate x
        <$> traverseVars proxy t
    T.Type x ->
      T.Type
        <$> traverseVars proxy x

instance VarTraversable x x' => VarTraversable (K.Bind x) x' where
  traverseVars proxy (K.Bind p v k t) =
    bindOne proxy v \v' ->
      K.Bind p v' k <$> traverseVars proxy t
