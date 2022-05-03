{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UnliftedFFITypes #-}
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
    Pxy,
    mkPxy,
  )
where

import AlgST.Syntax.Expression qualified as E
import AlgST.Syntax.Kind qualified as K
import AlgST.Syntax.Name
import AlgST.Syntax.Type qualified as T
import Control.Applicative
import Control.Category ((>>>))
import Control.Monad.Eta
import Control.Monad.Trans.Reader
import Data.Bitraversable
import Data.Foldable
import Data.Functor.Classes
import Data.Functor.Compose
import Data.Functor.Identity
import Data.Map.Strict qualified as Map
import Data.Maybe
import Data.Monoid qualified as M
import Data.Set qualified as Set
import Data.Singletons
import Data.Void
import GHC.Exts (Proxy#, proxy#)

type Pxy x y = Proxy# (x, y)

mkPxy :: () -> forall x y. Pxy x y
mkPxy _ = proxy#

class Applicative f => VarTraversal f x y where
  valueVariable :: Pxy x y -> E.XVar x -> ProgVar -> f (E.Exp y)
  typeVariable :: Pxy x y -> T.XVar x -> TypeVar -> f (T.Type y)

  useConstructor :: SingI scope => Pxy x y -> Name scope -> f (Name scope)

  -- | Binds a set of variables for the given computation.
  bind ::
    (Traversable t, SingI s) =>
    Pxy x y ->
    t (Name s) ->
    (t (Name s) -> f a) ->
    f a

bindOne ::
  forall x s f a y.
  (VarTraversal f x y, SingI s) =>
  Pxy x y ->
  Name s ->
  (Name s -> f a) ->
  f a
bindOne pxy v f = bind pxy (Identity v) (f . runIdentity)

newtype CollectFree = CollectFree
  { runCollect ::
      -- Bound variables
      ANameSet ->
      -- Accumulator
      ANameSet ->
      -- Result
      ANameSet
  }

instance Semigroup CollectFree where
  fv1 <> fv = CollectFree $ oneShot \bound -> oneShot \acc ->
    runCollect fv1 bound (runCollect fv bound acc)

instance Monoid CollectFree where
  mempty = CollectFree (const id)

instance x ~ y => VarTraversal (Const CollectFree) x y where
  typeVariable _ _ = varCollectFree
  valueVariable _ _ = varCollectFree
  useConstructor _ = pure

  bind _ vs f = Const . CollectFree $ oneShot \bound -> oneShot \acc ->
    let !bound' = foldl' (flip $ Set.insert . liftName) bound vs
     in runCollect (getConst (f vs)) bound' acc

-- Inserts the given variable into the set of free variables.
varCollectFree :: SingI s => Name s -> Const CollectFree b
varCollectFree (liftName -> v) = Const . CollectFree $ oneShot \bound -> oneShot \acc ->
  -- Don't include it if it is either bound or already recorded.
  if v `Set.member` bound || v `Set.member` acc
    then acc
    else Set.insert v acc

-- | Collects all free variables.
collectFree :: forall s x. VarTraversable (s x) x (s x) x => s x -> ANameSet
collectFree a =
  runCollect (getConst @_ @(s x) (traverseVars (mkPxy () @x @x) a)) mempty mempty

newtype Any = Any {runAny :: ANameSet -> Bool}
  deriving (Monoid) via (ANameSet -> M.Any)

instance Semigroup Any where
  fv1 <> fv2 = Any $ oneShot \intresting ->
    runAny fv1 intresting || runAny fv2 intresting

instance x ~ y => VarTraversal (Const Any) x y where
  valueVariable _ _ = anyVariable
  typeVariable _ _ = anyVariable
  useConstructor _ = pure

  -- When a variable is bound it will be removed from the set of intresting
  -- variables. If the set becomes empty we will short-circuit to False.
  bind _ vs f = Const . Any $ oneShot \intresting -> do
    let intresting' = foldl' (flip (Set.delete . liftName)) intresting vs
     in not (Set.null intresting') && runAny (getConst (f vs)) intresting'

anyVariable :: SingI s => Name s -> Const Any a
anyVariable = Const . Any . Set.member . liftName

-- | Checks if any of the variables in the given set are free in the given
-- piece of syntax.
anyFree :: forall s x. VarTraversable (s x) x (s x) x => ANameSet -> s x -> Bool
anyFree vars a
  | Set.null vars = False
  | otherwise = runAny (getConst @_ @(s x) (traverseVars (mkPxy () @x @x) a)) vars

data Substitutions x = Substitutions
  { progVarSubs :: !(NameMap Values (E.Exp x)),
    typeVarSubs :: !(NameMap Types (T.Type x))
  }

instance
  ( VarTraversable (E.XExp x) x (E.XExp y) y,
    E.SameX x y,
    VarTraversable (T.XType x) x (T.XType y) y,
    T.SameX x y
  ) =>
  VarTraversable (Substitutions x) x (Substitutions y) y
  where
  traverseVars pxy subs =
    Substitutions
      <$> traverse (traverseVars pxy) (progVarSubs subs)
      <*> traverse (traverseVars pxy) (typeVarSubs subs)

emptySubstitutions :: Substitutions x
emptySubstitutions = Substitutions Map.empty Map.empty

nullSubstitutions :: Substitutions x -> Bool
nullSubstitutions = (&&) <$> Map.null . progVarSubs <*> Map.null . typeVarSubs

typeSubstitions :: NameMap Types (T.Type x) -> Substitutions x
typeSubstitions s = emptySubstitutions {typeVarSubs = s}

termSubstitions :: NameMap Values (E.Exp x) -> Substitutions x
termSubstitions s = emptySubstitutions {progVarSubs = s}

instance (Monad m, x ~ y) => VarTraversal (ReaderT (Substitutions x) m) x y where
  valueVariable _ x = etaReaderT . asks . subVar (E.Var x) progVarSubs
  typeVariable _ x = etaReaderT . asks . subVar (T.Var x) typeVarSubs
  useConstructor _ = pure

  -- Remove the bound variables from the maps.
  bind _ vs f = etaReaderT do
    let removeVar subs =
          liftName >>> \case
            Left tv -> subs {typeVarSubs = Map.delete tv (typeVarSubs subs)}
            Right pv -> subs {progVarSubs = Map.delete pv (progVarSubs subs)}
    local (\s -> foldl' removeVar s vs) do
      f vs

subVar :: (Name s -> a) -> (Substitutions x -> NameMap s a) -> Name s -> Substitutions x -> a
subVar def f v = fromMaybe (def v) . Map.lookup v . f

applySubstitutions :: forall a x. VarTraversable a x a x => Substitutions x -> a -> a
applySubstitutions s a
  | nullSubstitutions s = a
  | otherwise = runReader (traverseVars (mkPxy () @x @x) a) s

-- | Substitute a single 'TypeVar'.
substituteType :: VarTraversable a x a x => NameMap Types (T.Type x) -> a -> a
substituteType = applySubstitutions . typeSubstitions

-- | Substitute a single 'ProgVar'.
substituteTerm :: VarTraversable a x a x => NameMap Values (E.Exp x) -> a -> a
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

class VarTraversable a x b y where
  traverseVars :: VarTraversal f x y => Pxy x y -> a -> f b

instance VarTraversable Void x Void y where
  traverseVars _ = pure

instance
  (VarTraversable a x a' y, VarTraversable b x b' y) =>
  VarTraversable (Either a b) x (Either a' b') y
  where
  traverseVars pxy = bitraverse (traverseVars pxy) (traverseVars pxy)

instance
  ( VarTraversable (E.XExp x) x (E.XExp y) y,
    E.SameX x y,
    VarTraversable (T.XType x) x (T.XType y) y,
    T.SameX x y
  ) =>
  VarTraversable (E.Exp x) x (E.Exp y) y
  where
  traverseVars pxy = \case
    E.Lit x l ->
      pure (E.Lit x l)
    E.Var x v ->
      valueVariable pxy x v
    E.Con x c ->
      E.Con x
        <$> useConstructor pxy c
    E.Abs x b ->
      E.Abs x
        <$> traverseVars pxy b
    E.App x e1 e2 ->
      E.App x
        <$> traverseVars pxy e1
        <*> traverseVars pxy e2
    E.Pair x e1 e2 ->
      E.Pair x
        <$> traverseVars pxy e1
        <*> traverseVars pxy e2
    E.UnLet x v mty e k -> do
      let unLet mty' e' (v', k') =
            E.UnLet x v' mty' e' k'
      unLet
        <$> traverse (traverseVars pxy) mty
        <*> traverseVars pxy e
        <*> bindOne pxy v \v' -> (v',) <$> traverseVars pxy k
    E.PatLet x v vs e k -> do
      let patLet e' (vs', k') =
            E.PatLet x v vs' e' k'
      patLet
        <$> traverseVars pxy e
        <*> bind pxy (Compose vs) \(Compose vs') -> (vs',) <$> traverseVars pxy k
    E.Rec x v ty e -> do
      let expRec ty' (v', e') =
            E.Rec x v' ty' e'
      expRec
        <$> traverseVars pxy ty
        <*> bindOne pxy v \v' -> (v',) <$> traverseVars pxy e
    E.Cond x eCond eThen eElse ->
      E.Cond x
        <$> traverseVars pxy eCond
        <*> traverseVars pxy eThen
        <*> traverseVars pxy eElse
    E.Case x e cases ->
      E.Case x
        <$> traverseVars pxy e
        <*> traverseVars pxy cases
    E.TypeAbs x b ->
      E.TypeAbs x
        <$> traverseVars pxy b
    E.TypeApp x e t ->
      E.TypeApp x
        <$> traverseVars pxy e
        <*> traverseVars pxy t
    E.New x t ->
      E.New x
        <$> traverseVars pxy t
    E.Select x c ->
      pure (E.Select x c)
    E.Fork x e ->
      E.Fork x
        <$> traverseVars pxy e
    E.Fork_ x e ->
      E.Fork_ x
        <$> traverseVars pxy e
    E.Exp x ->
      E.Exp
        <$> traverseVars pxy x

instance
  ( VarTraversable (E.XExp x) x (E.XExp y) y,
    E.SameX x y,
    VarTraversable (T.XType x) x (T.XType y) y,
    T.SameX x y
  ) =>
  VarTraversable (E.RecLam x) x (E.RecLam y) y
  where
  traverseVars pxy = \case
    E.RecTermAbs x b -> E.RecTermAbs x <$> traverseVars pxy b
    E.RecTypeAbs x b -> E.RecTypeAbs x <$> traverseVars pxy b

instance
  ( VarTraversable (E.XExp x) x (E.XExp y) y,
    E.SameX x y,
    VarTraversable (T.XType x) x (T.XType y) y,
    T.SameX x y,
    Traversable f,
    Traversable g
  ) =>
  VarTraversable (E.CaseMap' f g x) x (E.CaseMap' f g y) y
  where
  traverseVars pxy cm =
    E.CaseMap
      <$> traverse (traverseVars pxy) (E.casesPatterns cm)
      <*> traverse (traverseVars pxy) (E.casesWildcard cm)

instance
  ( VarTraversable (E.XExp x) x (E.XExp y) y,
    E.SameX x y,
    VarTraversable (T.XType x) x (T.XType y) y,
    T.SameX x y,
    Traversable f
  ) =>
  VarTraversable (E.CaseBranch f x) x (E.CaseBranch f y) y
  where
  traverseVars pxy b =
    bind pxy (Compose (E.branchBinds b)) \(Compose binds) -> do
      e <- traverseVars pxy (E.branchExp b)
      pure
        b
          { E.branchBinds = binds,
            E.branchExp = e
          }

instance
  ( VarTraversable (E.XExp x) x (E.XExp y) y,
    E.SameX x y,
    VarTraversable (T.XType x) x (T.XType y) y,
    T.SameX x y
  ) =>
  VarTraversable (E.Bind x) x (E.Bind y) y
  where
  traverseVars pxy (E.Bind x m v t e) = do
    let mkBind t' (v', e') =
          E.Bind x m v' t' e'
    mkBind
      <$> traverseVars pxy t
      <*> bindOne pxy v (\v' -> (v',) <$> traverseVars pxy e)

instance
  ( VarTraversable (T.XType x) x (T.XType y) y,
    T.SameX x y
  ) =>
  VarTraversable (T.Type x) x (T.Type y) y
  where
  traverseVars pxy = \case
    T.Unit x ->
      pure (T.Unit x)
    T.Arrow x m t u ->
      T.Arrow x m
        <$> traverseVars pxy t
        <*> traverseVars pxy u
    T.Pair x t u ->
      T.Pair x
        <$> traverseVars pxy t
        <*> traverseVars pxy u
    T.Session x p t u ->
      T.Session x p
        <$> traverseVars pxy t
        <*> traverseVars pxy u
    T.End x ->
      pure (T.End x)
    T.Forall x b ->
      T.Forall x
        <$> traverseVars pxy b
    T.Var x v ->
      typeVariable pxy x v
    T.Con x v ->
      pure (T.Con x v)
    T.App x t u ->
      T.App x
        <$> traverseVars pxy t
        <*> traverseVars pxy u
    T.Dualof x t ->
      T.Dualof x
        <$> traverseVars pxy t
    T.Negate x t ->
      T.Negate x
        <$> traverseVars pxy t
    T.Type x ->
      T.Type
        <$> traverseVars pxy x

instance VarTraversable a x b y => VarTraversable (K.Bind a) x (K.Bind b) y where
  traverseVars pxy (K.Bind p v k t) =
    bindOne pxy v \v' ->
      K.Bind p v' k <$> traverseVars pxy t
