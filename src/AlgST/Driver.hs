{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module AlgST.Driver
  ( Settings (..),
    Source,
    defaultSettings,
    addModuleSource,
    addModuleSourceIO,
    Driver,
    runDriver,
    parseAllModules,
  )
where

import AlgST.Parse.Parser qualified as P
import AlgST.Parse.Phase
import AlgST.Syntax.Module
import AlgST.Syntax.Name
import AlgST.Util.Error
import AlgST.Util.ErrorMessage
import Algebra.Graph.AdjacencyMap qualified as G
import Algebra.Graph.AdjacencyMap.Algorithm qualified as G (Cycle)
import Algebra.Graph.Labelled.AdjacencyMap qualified as LG
import Algebra.Graph.ToGraph qualified as G
import Control.Category ((>>>))
import Control.Concurrent
import Control.Exception
import Control.Monad.Cont
import Control.Monad.Reader
import Control.Monad.ST (RealWorld)
import Control.Scheduler hiding (traverse_)
import Data.Foldable
import Data.Function
import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as HM
import Data.IORef
import Data.List qualified as List
import Data.List.NonEmpty (NonEmpty (..), nonEmpty, (<|))
import Data.Maybe
import Data.Ord
import Data.Semigroup
import Data.Set ((\\))
import Data.Set qualified as Set
import Syntax.Base
import System.FilePath
import System.IO
import System.IO.Error

data Settings = Settings
  { driverSources :: !(HashMap ModuleName Source),
    driverSearchPaths :: [FilePath],
    driverDebugOutput :: Bool
  }
  deriving stock (Show)

data DriverState = DriverState
  { driverSettings :: !Settings,
    driverOutputLock :: !(MVar OutputMode),
    driverDeps :: !(IORef Dependencies),
    driverErrors :: !(IORef Bool)
  }

type Source = (FilePath, String)

type Dependencies = LG.AdjacencyMap ImportLocation ModuleName

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

newtype Driver a = Driver {unDriver :: ReaderT DriverState IO a}
  deriving newtype (Functor, Applicative, Monad, MonadIO)

runDriver :: OutputMode -> Settings -> Driver a -> IO (Either a a)
runDriver mode driverSettings m = do
  driverOutputLock <- newMVar mode
  driverDeps <- newIORef mempty
  driverErrors <- newIORef False
  a <- runDriverSt DriverState {..} m
  hasError <- readIORef driverErrors
  pure if hasError then Left a else Right a

runDriverSt :: DriverState -> Driver a -> IO a
runDriverSt dst (Driver m) = runReaderT m dst

askState :: Driver DriverState
askState = Driver ask

asksState :: (DriverState -> a) -> Driver a
asksState = Driver . asks

defaultSettings :: Settings
defaultSettings =
  Settings
    { driverSources = mempty,
      driverSearchPaths = mempty,
      driverDebugOutput = False
    }

addModuleSource :: ModuleName -> FilePath -> String -> Settings -> Settings
addModuleSource name fp src settings =
  settings {driverSources = HM.insert name (fp, src) (driverSources settings)}

addModuleSourceIO :: ModuleName -> FilePath -> Settings -> IO Settings
addModuleSourceIO name fp settings = do
  src <- readFile fp
  pure $ addModuleSource name fp src settings

data ModuleInfo x = ModuleInfo
  { modName :: ModuleName,
    modPath :: FilePath,
    modData :: Module x
  }

parseAllModules :: ModuleName -> Driver [ModuleInfo Parse]
parseAllModules firstName = do
  mods <- Driver . fmap catMaybes . withScheduler Par $ \scheduler -> do
    unDriver $ parseModule scheduler firstName
  deps <- liftIO . readIORef =<< asksState driverDeps
  for_ (cycleError <$> dependencyCycles deps) \case
    Left (fp, diag) -> displayDiagnostics fp [diag]
    Right diag -> displayDiagnostics "" [diag]
  pure mods

-- | Submits parsing of the given module to the scheduler. This operation
-- assumes that the module has not been submitted for parsing.
parseModule :: Scheduler RealWorld (Maybe (ModuleInfo Parse)) -> ModuleName -> Driver ()
parseModule scheduler name = do
  env <- askState
  mmodInfo <- findModule name
  when (isNothing mmodInfo) do
    setError
  liftIO $ for_ mmodInfo \(fp, src) -> scheduleWork scheduler $ runDriverSt env do
    driverOutput $ const $ putStrLn $ "Parsing " ++ unModuleName name
    let parseResult = P.runParser P.parseModule src
    case parseResult of
      Left errs -> do
        displayDiagnostics fp errs
        pure Nothing
      Right parsed -> do
        newDeps <- noteDependencies name fp parsed
        traverse_ (parseModule scheduler) newDeps
        pure $ Just ModuleInfo {modName = name, modPath = fp, modData = parsed}

findModule :: ModuleName -> Driver (Maybe (FilePath, String))
findModule name = withDebugOutput \_ dbg -> flip runContT (final dbg) do
  lift $ dbg $ "Locating module " ++ unModuleName name

  -- Check if it is a known virtual module.
  virtual <- lift $ asksState $ driverSettings >>> driverSources >>> HM.lookup name
  for_ virtual \res -> do
    -- It is. Early exit.
    lift $ dbg ".. found as a virtual module"
    ContT $ const $ pure $ Just res

  -- Not a virtual module. Look through the search paths instead.
  env <- lift askState
  liftIO do
    dbg ".. not a virtual module, looking through search paths instead"
    res <- tryIOError $ asum [runDriverSt env (tryRead dbg dir) | dir <- driverSearchPaths (driverSettings env)]
    dbg ".. search paths enumerated"
    pure $ either (const Nothing) Just res
  where
    tryRead :: DebugFn -> FilePath -> Driver (FilePath, String)
    tryRead dbg dir = do
      let fp = dir </> modulePath name
      dbg $ ".. ? " ++ fp
      (fp,) <$> readFile' fp `noteDebugException` \(e :: IOError) ->
        dbg $ ".. ⮑  " ++ displayException e
    final :: MonadIO m => DebugFn -> Maybe (FilePath, String) -> m (Maybe (FilePath, String))
    final dbg res = do
      dbg $ case res of
        Nothing -> "++ Module " ++ unModuleName name ++ " not found"
        Just (fp, _) -> "++ Module " ++ unModuleName name ++ " found at " ++ fp
      pure res

-- | Register the import dependencies for the given module and returns the set
-- of modules yet to be parsed.
noteDependencies :: ModuleName -> FilePath -> Module x -> Driver [ModuleName]
noteDependencies name fp mod = do
  depsRef <- asksState driverDeps
  let !newDeps = moduleDependencies name fp mod
  oldDeps <- liftIO $ atomicModifyIORef' depsRef \deps ->
    (deps <> newDeps, deps)
  pure $ Set.toList $ LG.vertexSet newDeps \\ LG.vertexSet oldDeps

dependencyCycles :: Dependencies -> [G.Cycle (ModuleName, ImportLocation)]
dependencyCycles deps =
  deps
    & G.toAdjacencyMap
    & go
    & fmap annotCycle
  where
    go deps = case G.topSort deps of
      Left c -> c : go (breakCycle c deps)
      Right _ -> []
    breakCycle = \case
      v :| [] -> G.removeEdge v v
      v :| w : _ -> G.removeEdge v w
    annotCycle c@(v0 :| _) =
      let go = \case
            v :| [] -> (v, LG.edgeLabel v v0 deps) :| []
            v :| v' : vs -> (v, LG.edgeLabel v v' deps) <| go (v' :| vs)
       in go c

cycleError :: G.Cycle (ModuleName, ImportLocation) -> Either (FilePath, Diagnostic) Diagnostic
cycleError ((m, iloc) :| []) = Left (importLocPath iloc, err)
  where
    err =
      PosError
        (pos iloc)
        [Error "Module", Error m, Error "imports itself."]
cycleError ((m0, iloc0) :| ms) =
  Right . unlocatedError . List.intercalate [ErrLine] $
    [Error "Cycle in module imports:"] :
    step "   Module" m0 iloc0
      ++ concatMap (uncurry $ step "   imports") ms
      ++ [[Error "   imports", Error m0]]
  where
    step s m iloc =
      [ [Error s, Error m],
        [ Error . MsgTag $
            "     at "
              ++ (if null (importLocPath iloc) then "«unknown»" else importLocPath iloc)
              ++ ":"
              ++ show (pos iloc)
        ]
      ]

moduleDependencies :: ModuleName -> FilePath -> Module x -> Dependencies
moduleDependencies thisName thisPath m =
  LG.edges
    [ thisName -< ImportLocation (p @- thisPath) >- target
      | p :@ Import {importTarget = target} <- moduleImports m
    ]
  where
    a -< e = (a, e)
    (a, e) >- b = (e, a, b)

setError :: Driver ()
setError = do
  ref <- asksState driverErrors
  liftIO $ writeIORef ref True

displayDiagnostics :: Foldable f => FilePath -> f Diagnostic -> Driver ()
displayDiagnostics fp diags
  | null diags =
    pure ()
  | otherwise = do
    setError
    driverOutput \mode ->
      putStrLn $ renderErrors mode fp $ toList diags

type OutputFn a = OutputMode -> IO a

type DebugFn = forall m. MonadIO m => String -> m ()

driverOutput :: OutputFn a -> Driver a
driverOutput f = do
  lock <- asksState driverOutputLock
  liftIO $ withMVar lock f

withDebugOutput ::
  ( (forall x. OutputFn x -> Driver x) ->
    DebugFn ->
    Driver a
  ) ->
  Driver a
withDebugOutput f = do
  env <- askState
  if driverDebugOutput $ driverSettings env
    then driverOutput \m -> runDriverSt env (f (\g -> liftIO (g m)) (liftIO . hPutStrLn stderr))
    else f driverOutput (const (pure ()))

noteDebugException :: Exception e => IO a -> (e -> IO b) -> Driver a
noteDebugException !m handler =
  asksState (driverSettings >>> driverDebugOutput)
    >>= liftIO . \case
      True -> m `catch` \e -> handler e *> throwIO e
      False -> m
