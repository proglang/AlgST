{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}

module AlgST.Driver.Dependencies
  ( DepVertex,
    Cycles (..),
    DepsGraph,
    emptyDepsGraph,
    Dependency (DependsOn),
    insertDependency,
    depsMember,
    removeCycles,
    traverseGraphPar,
    ImportLocation (..),
    importLocPath,
  )
where

import AlgST.Syntax.Name
import Algebra.Graph.AdjacencyMap qualified as G
import Algebra.Graph.AdjacencyMap.Algorithm qualified as G
import Control.Category ((>>>))
import Control.Monad.IO.Unlift
import Control.Scheduler
import Data.Coerce
import Data.Foldable
import Data.Function
import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as HM
import Data.Hashable
import Data.IORef
import Data.Kind
import Data.List.NonEmpty (NonEmpty (..), nonEmpty)
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

data Cycles
  = Acyclic
  | MaybeCyclic

type DepVertex = ModuleName

type DepsGraph :: Cycles -> Type
data DepsGraph cycles = DepsGraph
  { -- | A map from @(x,y)@ to the location where @x@ imported @y@.
    dgEdges :: !(HashMap Dependency ImportLocation),
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
    dgVerticesToDeps :: !(G.AdjacencyMap DepVertex),
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
    dgVerticesToUsedBy :: !(G.AdjacencyMap DepVertex)
  }

-- | The empty 'DepsGraph'.
emptyDepsGraph :: DepsGraph cycles
emptyDepsGraph = DepsGraph HM.empty G.empty G.empty

-- | Check if the given node is recorded in the dependency graph.
depsMember :: DepVertex -> DepsGraph acyclic -> Bool
depsMember v dg = G.hasVertex v (dgVerticesToDeps dg)

-- | Data type to help with understanding the direction of the depedency.
-- Consider using the constructor in its infix form:
--
-- > x `DependsOn` y
newtype Dependency = Dependency (DepVertex, DepVertex)
  deriving newtype (Eq, Ord, Hashable)

pattern DependsOn :: DepVertex -> DepVertex -> Dependency
pattern x `DependsOn` y = Dependency (x, y)

{-# COMPLETE DependsOn #-}

infix 6 `DependsOn`

instance Show Dependency where
  showsPrec p (x `DependsOn` y) =
    showParen (p > prec) $
      showsPrec (prec + 1) x . showString " `DependsOn` " . showsPrec (prec + 1) y
    where
      prec = 6

-- | Records a dependency in the graph.
insertDependency ::
  ImportLocation ->
  Dependency ->
  DepsGraph cycles ->
  DepsGraph MaybeCyclic
insertDependency loc (x `DependsOn` y) dg =
  DepsGraph
    { dgEdges = HM.insertWith (<>) (x `DependsOn` y) loc (dgEdges dg),
      dgVerticesToDeps = G.edge x y <> dgVerticesToDeps dg,
      dgVerticesToUsedBy = G.edge y x <> dgVerticesToUsedBy dg
    }

-- | Removes edges from the graph until it is acyclic.
--
-- The order of returned cycles is unspecified. The first edge of each cycle
-- corresponds to edge missing from the resulting graph.
removeCycles ::
  DepsGraph cycles ->
  (DepsGraph Acyclic, [G.Cycle (DepVertex, ImportLocation)])
removeCycles dg0@DepsGraph {dgEdges = labels} = go [] dg0
  where
    go cs dg = case G.topSort (dgVerticesToDeps dg) of
      Left c -> go (labelCycle c : cs) (breakCycle c dg)
      Right _ -> (coerce dg, cs)
    breakCycle c dg = do
      let (x, y) = case c of
            v :| [] -> (v, v)
            v :| w : _ -> (v, w)
      DepsGraph
        { dgEdges = HM.delete (x `DependsOn` y) (dgEdges dg),
          dgVerticesToDeps = G.removeEdge x y (dgVerticesToDeps dg),
          dgVerticesToUsedBy = G.removeEdge y x (dgVerticesToUsedBy dg)
        }
    labelCycle (v0 :| vs) = do
      let lookupLabel x y = case HM.lookup (x `DependsOn` y) labels of
            Nothing -> error "missing edge label"
            Just lbl -> lbl
      let f x (dep, annots) =
            (x, (x, lookupLabel x dep) : annots)
      let (v1, annots) = foldr f (v0, []) vs
      (v0, lookupLabel v0 v1) :| annots

data TraverseState a = TraverseState !Int [a]

-- | Execute an action for each node in the depdency graph. The execution is
-- paralellized as much as possible.
--
-- Each action gets the results from its dependencies as inputs. The result
-- corresponds to the list of all action outputs. The ordering of the list is
-- unpsecified.
traverseGraphPar ::
  forall a m.
  MonadUnliftIO m =>
  DepsGraph Acyclic ->
  ([a] -> DepVertex -> m a) ->
  m [a]
traverseGraphPar dg op = withScheduler Par \s ->
  askRunInIO >>= \runIO -> liftIO mdo
    -- For each vertex we create an action which waits for N inputs. When the
    -- N-th input arrives it runs `op`.
    --
    -- When `op` completes the action is tasked with sending the result to each
    -- depending vertex-action.
    let runOp :: [a] -> DepVertex -> IO a
        runOp bs a = do
          b <- runIO $ op bs a
          for_ (G.postSet a (dgVerticesToUsedBy dg)) \a' ->
            for_ (Map.lookup a' actions) \f ->
              f b
          pure b
    let superflousInput =
          fail "received input for already scheduled vertex"
    let vertexAction :: DepVertex -> Set.Set dep -> IO (a -> IO ())
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
        & liftIO
    pure ()
