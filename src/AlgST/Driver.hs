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
import Algebra.Graph.AdjacencyMap qualified as G
import Control.Category ((>>>))
import Control.Concurrent
import Control.Exception
import Control.Monad.Cont
import Control.Monad.Reader
import Control.Monad.ST (RealWorld)
import Control.Scheduler hiding (traverse_)
import Data.Foldable
import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as HM
import Data.IORef
import Data.Maybe
import Data.Set ((\\))
import Data.Set qualified as Set
import System.FilePath
import System.IO
import System.IO.Error

data Settings = Settings
  { driverSources :: !(HashMap ModuleName Source),
    driverSearchPaths :: [FilePath],
    driverDebugOutput :: Bool
  }

data DriverState = DriverState
  { driverSettings :: !Settings,
    driverOutputLock :: !(MVar OutputMode),
    driverDeps :: !(IORef Dependencies)
  }

type Source = (FilePath, String)

type Dependencies = G.AdjacencyMap ModuleName

newtype Driver a = Driver {unDriver :: ReaderT DriverState IO a}
  deriving newtype (Functor, Applicative, Monad, MonadIO)

runDriver :: OutputMode -> Settings -> Driver a -> IO a
runDriver mode driverSettings m = do
  driverOutputLock <- newMVar mode
  driverDeps <- newIORef mempty
  runDriverSt DriverState {..} m

runDriverSt :: DriverState -> Driver a -> IO a
runDriverSt dst (Driver m) = runReaderT m dst

askState :: Driver DriverState
askState = Driver ask

asksState :: (DriverState -> a) -> Driver a
asksState = Driver . asks

addModuleSource :: ModuleName -> FilePath -> String -> Settings -> Settings
addModuleSource name fp src settings =
  settings {driverSources = HM.insert name (fp, src) (driverSources settings)}

addModuleSourceIO :: ModuleName -> FilePath -> Settings -> IO Settings
addModuleSourceIO name fp settings = do
  src <- readFile fp
  pure $ addModuleSource name fp src settings

parseAllModules :: ModuleName -> Driver (HashMap ModuleName (FilePath, PModule))
parseAllModules firstName =
  Driver . fmap (HM.fromList . catMaybes) . withScheduler Par $ \scheduler -> do
    unDriver $ parseModule scheduler firstName

-- | Submits parsing of the given module to the scheduler. This operation
-- assumes that the module has not been submitted for parsing.
parseModule :: Scheduler RealWorld (Maybe (ModuleName, (FilePath, PModule))) -> ModuleName -> Driver ()
parseModule scheduler name = do
  env <- askState
  mmodInfo <- findModule name
  liftIO $ for_ mmodInfo \(fp, src) -> scheduleWork scheduler $ runDriverSt env do
    driverOutput $ const $ putStrLn $ "Parsing " ++ unModuleName name
    let parseResult = P.runParser P.parseModule src
    case parseResult of
      Left errs -> do
        displayDiagnostics fp errs
        pure Nothing
      Right parsed -> do
        newDeps <- noteDependencies name parsed
        traverse_ (parseModule scheduler) newDeps
        pure $ Just (name, (fp, parsed))

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
noteDependencies :: ModuleName -> Module x -> Driver [ModuleName]
noteDependencies name mod = do
  depsRef <- asksState driverDeps
  let !newDeps = moduleDependencies name mod
  oldDeps <- liftIO $ atomicModifyIORef' depsRef \deps ->
    (deps <> newDeps, deps)
  pure $ Set.toList $ G.vertexSet newDeps \\ G.vertexSet oldDeps

moduleDependencies :: ModuleName -> Module x -> Dependencies
moduleDependencies this =
  moduleImports
    >>> fmap (foldL importTarget)
    >>> G.vertices
    >>> G.connect (G.vertex this)

displayDiagnostics :: Foldable f => FilePath -> f Diagnostic -> Driver ()
displayDiagnostics fp diags = driverOutput \mode -> do
  putStr $ renderErrors mode fp $ toList diags

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
