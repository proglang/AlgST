{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}

module AlgST.Driver
  ( -- * Driver monad
    Driver,
    runDriver,

    -- * Settings
    Settings (..),
    Source,
    defaultSettings,
    setSearchPaths,
    addSearchPathFront,
    addSearchPathBack,
    addModuleSource,
    addModuleSourceIO,

    -- * Actions
    parseAllModules,
    renameAll,
    checkAll,
  )
where

import AlgST.Builtins
import AlgST.Driver.Dependencies
import AlgST.Parse.Parser qualified as P
import AlgST.Parse.Phase
import AlgST.Rename qualified as Rn
import AlgST.Rename.Fresh (runFresh)
import AlgST.Rename.Modules qualified as Rn
import AlgST.Syntax.Name
import AlgST.Syntax.Program
import AlgST.Typing (TcModule)
import AlgST.Typing qualified as Tc
import AlgST.Util (plural)
import AlgST.Util.Error
import AlgST.Util.ErrorMessage
import AlgST.Util.Output
import AlgST.Util.RecursiveLock
import Algebra.Graph.AdjacencyMap.Algorithm qualified as G (Cycle)
import Control.Category ((>>>))
import Control.DeepSeq (force)
import Control.Exception
import Control.Monad.Cont
import Control.Monad.IO.Unlift
import Control.Monad.Reader
import Control.Monad.ST (RealWorld)
import Control.Monad.Validate
import Control.Scheduler hiding (Scheduler, traverse_)
import Control.Scheduler qualified as S
import Data.Foldable
import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as HM
import Data.IORef
import Data.List qualified as List
import Data.List.NonEmpty (NonEmpty (..))
import Data.Maybe
import Data.Sequence (Seq (..))
import Data.Sequence qualified as Seq
import Syntax.Base
import System.FilePath
import System.IO
import System.IO.Error

data Settings = Settings
  { driverSources :: !(HashMap ModuleName Source),
    driverSearchPaths :: !(Seq FilePath),
    driverVerboseSearches :: !Bool,
    driverDebugOutput :: !Bool,
    driverSequential :: !Bool,
    driverShowDepsGraph :: !Bool
  }
  deriving stock (Show)

data DriverState = DriverState
  { driverSettings :: !Settings,
    driverErrors :: !(IORef Bool),
    driverOutputLock :: !(RecursiveLock OutputMode)
  }

type Source = (FilePath, String)

type Scheduler = S.Scheduler RealWorld

type DepsTracker = IORef (DepsGraph MaybeCyclic)

newtype Driver a = Driver {unDriver :: ReaderT DriverState IO a}
  deriving newtype (Functor, Applicative, Monad, MonadIO, MonadUnliftIO)

data ErrorAbortException = ErrorAbortException
  deriving stock (Show)

instance Exception ErrorAbortException

runDriver :: OutputMode -> Settings -> Driver a -> IO (Maybe a)
runDriver mode driverSettings m = do
  driverErrors <- newIORef False
  driverOutputLock <- newRecursiveLockIO mode
  res <- try @ErrorAbortException $ runDriverSt DriverState {..} m
  hasError <- readIORef driverErrors
  case res of
    Right a | not hasError -> pure (Just a)
    _ -> pure Nothing

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
      driverVerboseSearches = False,
      driverDebugOutput = False,
      driverSequential = False,
      driverShowDepsGraph = False
    }

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

-- | Replace the moudle search paths with the given list.
--
-- See 'addSearchPathFront' and 'addSearchPathBack' for adding entries to the
-- existing list.
setSearchPaths :: [FilePath] -> Settings -> Settings
setSearchPaths paths s = s {driverSearchPaths = Seq.fromList paths}

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

-- | Checks if the driver is in sequential mode ('driverSequential'). If so the
-- returned computation strategy will be 'Seq', otherwise it will be the given
-- strategy.
askStrategy :: Driver S.Comp
askStrategy = do
  isSeq <- asksState $ driverSettings >>> driverSequential
  pure $! if isSeq then Seq else Par

parScheduled :: (Scheduler a -> Driver b) -> Driver [a]
parScheduled m = do
  strat <- askStrategy
  Driver . withScheduler strat $ unDriver . m

addTask :: Scheduler a -> Driver a -> Driver ()
addTask scheduler m = do
  env <- askState
  liftIO $ scheduleWork scheduler $ runDriverSt env m

data ParsedModule = ParsedModule
  { pmName :: ModuleName,
    pmPath :: FilePath,
    pmModule :: PModule
  }

-- | Parse the given module and all dependencies. The result does not contain
-- any modules where errors occured.
parseAllModules :: ModuleName -> Driver (DepsGraph Acyclic, [ParsedModule])
parseAllModules firstName = do
  depsRef <- liftIO $ newIORef emptyDepsGraph
  mods <- parScheduled $ \scheduler -> do
    parseModule scheduler depsRef mempty firstName
  finalDeps <- liftIO $ readIORef depsRef

  outputDeps <- asksState $ driverSettings >>> driverShowDepsGraph
  when outputDeps $ output \mode -> do
    let header = applyStyle mode styleBold $ showString "== Dependencies =="
    hPutStrLn stderr $ header $ '\n' : exportTextual finalDeps

  let (acyclicDeps, cycles) = removeCycles finalDeps
  when (not (null cycles) && outputDeps) $ output \mode -> do
    let header = applyStyle mode styleBold $ showString "== Acyclic Dependencies =="
    hPutStrLn stderr $ header $ '\n' : exportTextual acyclicDeps

  for_ cycles $
    cycleError >>> \case
      Left (fp, diag) -> reportErrors fp [diag]
      Right diag -> reportErrors "" [diag]
  pure (acyclicDeps, catMaybes mods)

-- | Tries to locate the source code for the module with the given name using
-- the drivers settings (see 'Settings', 'driverSources', 'driverSearchPaths').
--
-- When the code was located successfully it is submitted for parsing using the
-- given scheduler (see 'parseModuleNow'). When locating the module's source
-- code fails an error is emitted.
parseModule ::
  -- | Where to schedule parsing of the module.
  Scheduler (Maybe ParsedModule) ->
  -- | Where to note down the inter-module dependencies.
  DepsTracker ->
  -- | Where this module was imported from. Used only for error messages.
  ImportLocation ->
  -- | Name of the module.
  ModuleName ->
  Driver ()
parseModule scheduler depsRef iloc name = do
  mmodInfo <- findModule name
  case mmodInfo of
    Nothing -> do
      reportErrors (importLocPath iloc) [missingModuleError (pos iloc) name]
    Just (fp, src) -> do
      addTask scheduler $ parseModuleNow scheduler depsRef name fp src

-- | Immediately begin parsing of the provided module. Any unparsed
-- dependencies are scheduled for parsing using the provided scheduler.
parseModuleNow ::
  -- | Where to schedule the dependent unparsed modules.
  Scheduler (Maybe ParsedModule) ->
  -- | Where to note down the inter-module dependencies.
  DepsTracker ->
  -- | Name of the module.
  ModuleName ->
  -- | Path to the code of the module. Used only for error messages.
  FilePath ->
  -- | Source code of the module.
  String ->
  Driver (Maybe ParsedModule)
parseModuleNow scheduler depsRef moduleName modulePath moduleSource = do
  outputString $ "Parsing " ++ unModuleName moduleName
  let parseResult = P.runParser P.parseModule moduleSource
  case parseResult of
    Left errs -> do
      reportErrors modulePath errs
      pure Nothing
    Right parsed -> do
      newDeps <- noteDependencies depsRef moduleName modulePath parsed
      traverse_ (uncurry $ parseModule scheduler depsRef) newDeps
      pure . Just $
        ParsedModule
          { pmName = moduleName,
            pmPath = modulePath,
            pmModule = parsed
          }

renameAll ::
  DepsGraph Acyclic ->
  [ParsedModule] ->
  Driver [(DepVertex, Rn.RnModule)]
renameAll dg mods = do
  strat <- askStrategy
  filterResults <$> traverseGraphPar strat dg \deps name -> do
    case HM.lookup name modsByName of
      Nothing -> pure (name, Rn.emptyModuleMap, Nothing)
      Just pm -> rename pm deps
  where
    modsByName = HM.fromList [(pmName pm, pm) | pm <- mods]
    filterResults xs = [(n, m) | (n, _, Just m) <- xs]

    rename pm deps = do
      let (rnMap, rnAction) =
            -- Insert a 'ImportAll Builtins' here.
            Rn.renameModule
              (pmName pm)
              (pmModule pm)
                { moduleImports =
                    defaultPos
                      @- Import
                        { importTarget = BuiltinsModule,
                          importQualifier = emptyModuleName,
                          importSelection = ImportAll defaultPos HM.empty HM.empty
                        } :
                    moduleImports (pmModule pm)
                }
      let availableImports =
            HM.fromList $
              (BuiltinsModule, builtinsModuleMap) :
                [(depName, depGlobals) | (depName, depGlobals, _) <- deps]
      case runValidate (rnAction availableImports) of
        Left errs -> do
          reportErrors (pmPath pm) errs
          pure (pmName pm, rnMap, Nothing)
        Right rnMod -> do
          pure (pmName pm, rnMap, Just rnMod)

checkAll :: DepsGraph Acyclic -> [ParsedModule] -> Driver TcModule
checkAll dg parsed = do
  renamed <- renameAll dg parsed

  -- TODO: Think about in which cases we can/want to progess with type checking
  -- after (partially) failed renaming. For now we only continue if there have
  -- not been any errors up to this point.
  checkNoError

  -- Type checking is done by merging all the modules together. This is safe to
  -- do because after renaming all names are qualified by their module.
  --
  -- Type checking has to run inside 'Fresh'. We use a name which is not a
  -- valid module name to ensure uniqueness.
  --
  -- FIXME: By doing this we loose the possibility for file specific error
  -- messages.
  let merge a b =
        Module
          { moduleTypes = moduleTypes a <> moduleTypes b,
            moduleValues = moduleValues a <> moduleValues b,
            moduleSigs = moduleSigs a <> moduleSigs b,
            -- No need to keep track of all the imports.
            moduleImports = []
          }
  -- Begin merging from the builtins module.
  let bigModule = foldl' merge builtins . fmap snd $ renamed
  case runFresh (ModuleName "$TC") $ Tc.checkModule bigModule of
    Left errs -> do
      reportErrors "" errs
      fatalErrors
    Right res -> do
      pure res

missingModuleError :: Pos -> ModuleName -> Diagnostic
missingModuleError loc name = PosError loc [Error "Cannot locate module", Error name]
{-# NOINLINE missingModuleError #-}

findModule :: ModuleName -> Driver (Maybe (FilePath, String))
findModule name = uninterleavedDebugOutput $ flip runContT final do
  lift $ debug $ "Locating module ‘" ++ unModuleName name ++ "’"

  -- Check if it is a known virtual module.
  virtual <- lift $ asksState $ driverSettings >>> driverSources >>> HM.lookup name
  for_ virtual \res -> do
    -- It is. Early exit.
    lift $ debug ".. found as a virtual module"
    ContT $ const $ pure $ Just res

  -- Not a virtual module. Look through the search paths instead.
  env <- lift askState
  let paths = driverSearchPaths $ driverSettings env
  let npaths = plural paths "one search path" $ show (length paths) ++ " search paths"
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
noteDependencies ::
  DepsTracker ->
  ModuleName ->
  FilePath ->
  Module x ->
  Driver [(ImportLocation, ModuleName)]
noteDependencies depsRef name fp mod = do
  let depList = moduleDependencies fp mod
  debug . unwords $
    [ "‘" ++ unModuleName name ++ "’",
      "has",
      plural depList "one dependency" $
        show (length depList) ++ " dependencies"
    ]
  -- Update the dependency graph. This step also signals to any other workers
  -- that this worker will be responsible for delegating parsing of any
  -- unparsed dependencies.
  oldDeps <- liftIO $ atomicModifyIORef' depsRef \deps -> do
    let add (iloc, target) = insertDependency iloc (name `DependsOn` target)
    (foldl' (flip add) deps depList, deps)
  -- Return the list of unparsed dependencies. Those are the ones not appearing
  -- as vertices in `oldDeps`.
  let isUnparsed (_, m) = m /= name && not (depsMember m oldDeps)
  pure $ filter isUnparsed depList

moduleDependencies :: FilePath -> Module x -> [(ImportLocation, ModuleName)]
moduleDependencies thisPath m =
  [ (ImportLocation (p @- thisPath), target)
    | p :@ Import {importTarget = target} <- moduleImports m
  ]

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

checkNoError :: Driver ()
checkNoError = do
  ref <- asksState driverErrors
  err <- liftIO $ readIORef ref
  when err fatalErrors

fatalErrors :: Driver a
fatalErrors = liftIO $ throwIO ErrorAbortException

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
outputString s = do
  -- Force the string outside the lock.
  _ <- liftIO . evaluate $ force s
  output . const $ putStrLn s

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
