{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}

module AlgST.Driver.Dependencies where

import Algebra.Graph.AdjacencyMap qualified as G
import Control.Category ((>>>))
import Control.Scheduler
import Data.Foldable
import Data.Function
import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as HM
import Data.Hashable
import Data.IORef
import Data.Kind
import Data.List.NonEmpty (nonEmpty)
import Data.Map qualified as Map
import Data.Ord
import Data.Semigroup
import Data.Set qualified as Set
import Syntax.Base

newtype ImportLocation = ImportLocation (Located FilePath)

importLocPath :: ImportLocation -> FilePath
importLocPath (ImportLocation iloc) = unL iloc

instance Position ImportLocation where
  pos (ImportLocation iloc) = pos iloc

-- | Two 'ImportLocation' values are considered equal if their contained 'Pos'
-- values are equal.
--
-- The stored 'FilePath' is not considered. this is mostly a slight
-- optimization since all edge labels from a module should originate from the
-- same source file.
instance Eq ImportLocation where
  a == b = compare a b == EQ

-- | See 'Eq' instance.
instance Ord ImportLocation where
  compare = comparing pos

instance Semigroup ImportLocation where
  a <> b = mconcat [a, b]
  sconcat = toList >>> mconcat
  stimes = stimesIdempotentMonoid

instance Monoid ImportLocation where
  mempty = ImportLocation $ defaultPos @- ""
  mconcat = filter (/= mempty) >>> nonEmpty >>> foldMap minimum

type Acyclic = True

type DepsGraph :: Bool -> Type -> Type
data DepsGraph acyclic a = DepsGraph
  { -- | A map from @(x,y)@ to the location where @x@ imported @y@.
    dgEdges :: !(HashMap (a, a) ImportLocation),
    -- | Vertices are conntected to the vertices they depend on.
    --
    -- E.g. @X@ depends on @Y@ and @Z@, and @Y@ depends on @Z@ gives
    --
    -- >  Z <-- Y
    -- >  ^     ^
    -- >  |     |
    -- >  +---- X
    --
    -- This is the transposition of 'dgVerticesToUsedBy'.
    dgVerticesToDeps :: !(G.AdjacencyMap a),
    -- | Vertices are conncted to the vertices they are used by.
    --
    -- E.g. @X@ depends on @Y@ and @Z@, and @Y@ depends on @Z@ gives
    --
    -- >  Z --> Y
    -- >  |     |
    -- >  |     v
    -- >  +---> X
    --
    -- This is the transposition of 'dgVerticesToDeps'.
    dgVerticesToUsedBy :: !(G.AdjacencyMap a)
  }

data Dependency a = DependsOn a a

insertDependency ::
  (Ord a, Hashable a) =>
  ImportLocation ->
  Dependency a ->
  DepsGraph acyclic a ->
  DepsGraph False a
insertDependency loc (x `DependsOn` y) dg =
  DepsGraph
    { dgEdges = HM.insertWith (<>) (x, y) loc (dgEdges dg),
      dgVerticesToDeps = G.edge x y <> dgVerticesToUsedBy dg,
      dgVerticesToUsedBy = G.edge y x <> dgVerticesToUsedBy dg
    }

data TraverseState a = TraverseState !Int [a]

traverseGraphPar :: forall a b. Ord a => DepsGraph Acyclic a -> ([b] -> a -> IO b) -> IO [b]
traverseGraphPar dg op = withScheduler Par \s -> mdo
  -- For each vertex we create an action which waits for N inputs. When the
  -- N-th input arrives it runs `op`.
  --
  -- When `op` completes the action is tasked with sending the result to each
  -- depending vertex-action.
  let runOp :: [b] -> a -> IO b
      runOp bs a = do
        b <- op bs a
        for_ (G.postSet a (dgVerticesToUsedBy dg)) \a' ->
          for_ (Map.lookup a' actions) \f ->
            f b
        pure b
  let superflousInput =
        fail "received input for already scheduled vertex"
  let vertexAction :: a -> Set.Set dep -> IO (b -> IO ())
      vertexAction a deps
        | Set.null deps = do
          scheduleWork s $ runOp [] a
          pure $ const superflousInput
        | otherwise = do
          r <- newIORef $ Just $ TraverseState (Set.size deps) []
          pure \b -> do
            bs <- atomicModifyIORef' r \case
              Nothing -> (Nothing, Nothing)
              Just (TraverseState 1 bs) -> do
                (Nothing, Just (b : bs))
              Just (TraverseState n bs) -> do
                (Just $! TraverseState (n - 1) (b : bs), Just [])
            case bs of
              Just [] -> pure ()
              Just bs -> scheduleWork s $ runOp bs a
              Nothing -> superflousInput
  actions <-
    dgVerticesToDeps dg
      & G.adjacencyMap
      & Map.traverseWithKey vertexAction
  pure ()
