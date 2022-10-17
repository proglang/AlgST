{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

module AlgST.Syntax.Destructure where

import AlgST.Syntax.Expression qualified as E
import AlgST.Syntax.Kind (Multiplicity)
import AlgST.Syntax.Kind qualified as K
import AlgST.Syntax.Name
import AlgST.Syntax.Phases
import AlgST.Syntax.Traversal
import AlgST.Syntax.Type qualified as T
import Data.Set qualified as Set

pattern Arrow ::
  ( HasPos (T.XCon x),
    SynTraversable (E.XExp x) x (E.XExp x) x,
    SynTraversable (T.XType x) x (T.XType x) x
  ) =>
  (T.Specificity -> Multiplicity -> T.Type x -> T.Type x -> T.Type x)
pattern Arrow s m t u <- (appArrow -> Just (s, m, t, u))

pattern TArrow :: K.Bind (XStage x) (T.Type x) -> T.Type x
pattern TArrow b <- (appTArrow -> Just b)

-- | Tries to destructure a type into into domain and codomain of an arrow.
-- This includes applying the forall isomorphism to push quantified type
-- variables further down if allowed.
appArrow ::
  ( HasPos (T.XCon x),
    SynTraversable (E.XExp x) x (E.XExp x) x,
    SynTraversable (T.XType x) x (T.XType x) x
  ) =>
  T.Type x ->
  Maybe (T.Specificity, Multiplicity, T.Type x, T.Type x)
appArrow = go id Set.empty
  where
    go prependPushed pushed = \case
      T.Arrow _ s m t u
        | not (liftNameSet pushed `anyFree` t) ->
            Just (s, m, t, prependPushed u)
      T.Forall x (K.Bind x' v k t) ->
        go
          (prependPushed . T.Forall x . K.Bind x' v k)
          (Set.insert v pushed)
          t
      _ ->
        Nothing

appTArrow :: T.Type x -> Maybe (K.Bind (XStage x) (T.Type x))
appTArrow = go id
  where
    go prependArrows = \case
      T.Forall _ (K.Bind x' v k t) ->
        Just (K.Bind x' v k $ prependArrows t)
      T.Arrow x s m t u ->
        go (prependArrows . T.Arrow x s m t) u
      _ ->
        Nothing
