{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module AlgST.Driver
  ( -- * Driver monad
    Driver,
    runDriver,

    -- * Settings
    Settings (..),
    Source,
    defaultSettings,
    addSearchPathFront,
    addSearchPathBack,
    addModuleSource,
    addModuleSourceIO,
    enableDebugMessages,

    -- * Actions
    parseAllModules,
  )
where

import AlgST.Parse.Parser qualified as P
import AlgST.Parse.Phase
import AlgST.Syntax.Module
import AlgST.Syntax.Name
import AlgST.Util (plural)
import AlgST.Util.Error
import AlgST.Util.ErrorMessage
import AlgST.Util.RecursiveLock
import Algebra.Graph.AdjacencyMap qualified as G
import Algebra.Graph.AdjacencyMap.Algorithm qualified as G (Cycle)
import Algebra.Graph.Labelled.AdjacencyMap qualified as LG
import Algebra.Graph.ToGraph qualified as G
import Control.Category ((>>>))
import Control.Exception
import Control.Monad.Cont
import Control.Monad.Reader
import Control.Monad.ST (RealWorld)
import Control.Scheduler hiding (Scheduler, traverse_)
import Control.Scheduler qualified as S
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
import Data.Sequence (Seq (..))
import Syntax.Base
import System.FilePath
import System.IO
import System.IO.Error

data Settings = Settings
  { driverSources :: !(HashMap ModuleName Source),
    driverSearchPaths :: !(Seq FilePath),
    driverDebugOutput :: Bool
  }
  deriving stock (Show)

data DriverState = DriverState
  { driverSettings :: !Settings,
    driverDeps :: !(IORef Dependencies),
    driverErrors :: !(IORef Bool),
    driverOutputLock :: !(RecursiveLock OutputMode)
  }

type Source = (FilePath, String)

type Dependencies = LG.AdjacencyMap ImportLocation ModuleName

type ParseResult = Maybe (ModuleInfo Parse)

type Scheduler = S.Scheduler RealWorld ParseResult

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
  driverDeps <- newIORef mempty
  driverErrors <- newIORef False
  driverOutputLock <- newRecursiveLockIO mode
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

enableDebugMessages :: Bool -> Settings -> Settings
enableDebugMessages !b s = s {driverDebugOutput = b}

-- | Insert a module search path at the front.
--
-- Search paths a traversed front to back to locate a module source.
addSearchPathFront :: FilePath -> Settings -> Settings
addSearchPathFront fp s = s {driverSearchPaths = fp :<| driverSearchPaths s}

-- | Insert a module search path at the back.
--
-- Search paths a traversed front to back to locate a module source.
addSearchPathBack :: FilePath -> Settings -> Settings
addSearchPathBack fp s = s {driverSearchPaths = driverSearchPaths s :|> fp}

-- | Register the source code for the given module. A directly registered
-- module has preference over a module found at a search path. The given file
-- path is used for error messages only.
addModuleSource :: ModuleName -> FilePath -> String -> Settings -> Settings
addModuleSource name fp src settings =
  settings {driverSources = HM.insert name (fp, src) (driverSources settings)}

-- | Read the source code for the given module from the file system and
-- register it using 'addModuleSource'.
addModuleSourceIO :: ModuleName -> FilePath -> Settings -> IO Settings
addModuleSourceIO name fp settings = do
  src <- readFile fp
  pure $ addModuleSource name fp src settings

data ModuleInfo x = ModuleInfo
  { modName :: ModuleName,
    modPath :: FilePath,
    modData :: Module x
  }

-- | Parse the given module and all dependencies. The result does not contain
-- any modules where errors occured.
parseAllModules :: ModuleName -> Driver [ModuleInfo Parse]
parseAllModules firstName = do
  mods <- Driver . fmap catMaybes . withScheduler Par $ \scheduler -> do
    unDriver $ parseModule scheduler mempty firstName
  deps <- liftIO . readIORef =<< asksState driverDeps
  for_ (cycleError <$> dependencyCycles deps) \case
    Left (fp, diag) -> reportErrors fp [diag]
    Right diag -> reportErrors "" [diag]
  pure mods

-- | Tries to locate the source code for the module with the given name using
-- the drivers settings (see 'Settings', 'driverSources', 'driverSearchPaths').
--
-- When the code was located successfully it is submitted for parsing using the
-- given scheduler (see 'parseModuleNow'). When locating the module's source
-- code fails an error is emitted.
parseModule ::
  -- | Where to schedule parsing of the module.
  Scheduler ->
  -- | Where this module was imported from. Used only for error messages.
  ImportLocation ->
  -- | Name of the module.
  ModuleName ->
  Driver ()
parseModule scheduler iloc name = do
  mmodInfo <- findModule name
  case mmodInfo of
    Nothing -> do
      reportErrors (importLocPath iloc) [missingModuleError (pos iloc) name]
    Just (fp, src) -> do
      env <- askState
      liftIO . scheduleWork scheduler . runDriverSt env $
        parseModuleNow scheduler name fp src

-- | Immediately begin parsing of the provided module. Any unparsed
-- dependencies are scheduled for parsing using the provided scheduler.
parseModuleNow ::
  -- | Where to schedule the dependent unparsed modules.
  Scheduler ->
  -- | Name of the module.
  ModuleName ->
  -- | Path to the code of the module. Used only for error messages.
  FilePath ->
  -- | Source code of the module.
  String ->
  Driver ParseResult
parseModuleNow scheduler moduleName modulePath moduleSource = do
  outputString $ "Parsing " ++ unModuleName moduleName
  let parseResult = P.runParser P.parseModule moduleSource
  case parseResult of
    Left errs -> do
      reportErrors modulePath errs
      pure Nothing
    Right parsed -> do
      newDeps <- noteDependencies moduleName modulePath parsed
      traverse_ (uncurry $ parseModule scheduler) newDeps
      pure $ Just ModuleInfo {modName = moduleName, modPath = modulePath, modData = parsed}

missingModuleError :: Pos -> ModuleName -> Diagnostic
missingModuleError loc name = PosError loc [Error "Cannot locate module", Error name]
{-# NOINLINE missingModuleError #-}

findModule :: ModuleName -> Driver (Maybe (FilePath, String))
findModule name = uninterleavedDebugOutput $ flip runContT final do
  lift $ debug $ "Locating module " ++ unModuleName name

  -- Check if it is a known virtual module.
  virtual <- lift $ asksState $ driverSettings >>> driverSources >>> HM.lookup name
  for_ virtual \res -> do
    -- It is. Early exit.
    lift $ debug ".. found as a virtual module"
    ContT $ const $ pure $ Just res

  -- Not a virtual module. Look through the search paths instead.
  env <- lift askState
  let paths = driverSearchPaths $ driverSettings env
  let npaths = show (length paths) ++ plural (length paths) "search path" "search paths"
  lift $ debug $ ".. not a virtual module, looking through " ++ npaths ++ " instead"
  res <- liftIO . tryIOError . asum $ runDriverSt env . tryRead <$> paths
  lift $ debug $ ".. " ++ npaths ++ " enumerated"
  pure $ either (const Nothing) Just res
  where
    tryRead :: FilePath -> Driver (FilePath, String)
    tryRead dir = do
      let fp = dir </> modulePath name
      debug $ ".. ? " ++ fp
      (fp,) <$> readFile' fp `debugTry` \case
        Left (e :: IOError) -> debug $ ".. ⮑  ✗ " ++ displayException e
        Right _ -> debug ".. ⮑  ✔"
    final :: Maybe (FilePath, String) -> Driver (Maybe (FilePath, String))
    final res = do
      debug $ case res of
        Nothing -> "++ Module " ++ unModuleName name ++ " not found"
        Just (fp, _) -> "++ Module " ++ unModuleName name ++ " found at " ++ fp
      pure res

-- | Register the import dependencies for the given module and returns the set
-- of modules yet to be parsed.
noteDependencies :: ModuleName -> FilePath -> Module x -> Driver [(ImportLocation, ModuleName)]
noteDependencies name fp mod = do
  depsRef <- asksState driverDeps
  let depList = moduleDependencies fp mod
  -- We calculate the graph strictly so that we reduce the amount of time we
  -- spend in the body of `atomicModifyIORef'`.
  let !depGraph = LG.overlays [LG.edge iloc name target | (iloc, target) <- depList]
  -- Update the dependency graph. This step also signals to any other workers
  -- that this worker will be responsible for delegating parsing of any
  -- unparsed dependencies.
  oldDeps <- liftIO $ atomicModifyIORef' depsRef \deps ->
    (deps <> depGraph, deps)
  -- Return the list of unparsed dependencies. Those are the ones not appearing
  -- as vertices in `oldDeps`.
  let isUnparsed (_, m) = m /= name && not (LG.hasVertex m oldDeps)
  pure $ filter isUnparsed depList

moduleDependencies :: FilePath -> Module x -> [(ImportLocation, ModuleName)]
moduleDependencies thisPath m =
  [ (ImportLocation (p @- thisPath), target)
    | p :@ Import {importTarget = target} <- moduleImports m
  ]

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

setError :: Driver ()
setError = do
  ref <- asksState driverErrors
  liftIO $ writeIORef ref True

-- | Report the errors to the user.
reportErrors :: Foldable f => FilePath -> f Diagnostic -> Driver ()
reportErrors fp diags
  | null diags =
    pure ()
  | otherwise = do
    setError
    output \mode -> putStrLn $ renderErrors mode fp $ toList diags

-- | Executes the given function with the 'driverOutputLock' held.
--
-- This function is re-entrant.
output :: (OutputMode -> IO a) -> Driver a
output f = do
  env <- askState
  liftIO $ withRecursiveLock (driverOutputLock env) f

-- | Writes the given string to 'stdout' using 'output'.
outputString :: String -> Driver ()
outputString = output . const . putStrLn

-- | Writes the given string to 'stderr' using 'output' if debug messages are
-- enabled (see 'driverDebugOutput').
debug :: String -> Driver ()
debug str = do
  debug <- asksState $ driverDebugOutput . driverSettings
  when debug $ outputString str

-- | When debug messages are enabled (see 'driverDebugOutput') this function
-- executes the given action with the output loock held (see 'output' and
-- 'driverOutputLock'). When debug message are not enabled it behaves like the
-- identity function.
--
-- The use case is to group related debug messages together. Note that this
-- negatively impacts the amount of effective concurrency in the driver.
uninterleavedDebugOutput :: Driver a -> Driver a
uninterleavedDebugOutput m = do
  env <- askState
  let debug = driverDebugOutput . driverSettings $ env
  if debug then output $ const $ runDriverSt env m else m

-- | When debug output is enabled the action @debugTry m handler@ installs an
-- exception handler during the execution of @m@. Afterwards @handler@ is
-- executed with either the obtained result or the caught exeption. If an
-- exception was thrown it will be rethrown after @handler@ returns.
--
-- When debug output is not enabled this function ignores its second argument
-- and returns @m@ unchanged.
debugTry :: Exception e => IO a -> (Either e a -> Driver b) -> Driver a
debugTry !m handler = do
  env <- askState
  liftIO
    if driverDebugOutput $ driverSettings env
      then try m >>= \r -> runDriverSt env (handler r) >> either throwIO pure r
      else m
