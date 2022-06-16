{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}

module AlgST.Driver.Output
  ( OutputHandle,
    nullHandle,
    withOutput,
    outputStr,
    outputStrLn,
    outputShow,
    outputLnS,
    outputS,

    -- ** Sticky messages
    -- $sticky
    outputSticky,
    clearSticky,

    -- * Sticky progress counters
    Counter,
    newCounter,
    newZeroCounter,
    newCounterStart,
    counterDone,
    CounterState (..),
    zeroCounter,
    counterRunningL,
    counterFinishedL,
    counterOverallL,
    counterTitleL,
    counterUpdate,
    wrapCounter,
  )
where

import AlgST.Util.Lenses
import Control.Category ((>>>))
import Control.Concurrent
import Control.Concurrent.Async qualified as Async
import Control.Concurrent.STM
import Control.Exception
import Control.Foldl qualified as L
import Control.Monad.IO.Unlift
import Control.Monad.State.Strict
import Data.Foldable
import Data.Functor
import Data.List.NonEmpty (NonEmpty (..))
import Data.Maybe
import Data.Monoid
import Lens.Family2
import System.Console.ANSI qualified as ANSI
import System.IO
import System.IO.Unsafe (unsafeDupablePerformIO)

newtype Sticky = Sticky String

emptySticky :: Sticky
emptySticky = Sticky ""

newtype OutputHandle = OutputHandle ActionBuffer

instance Show OutputHandle where
  show = \case
    OutputHandle NullBuffer -> "nullHandle"
    OutputHandle _ -> "OutputHandle{}"

nullHandle :: OutputHandle
nullHandle = OutputHandle $ unsafeDupablePerformIO $ newActionBufferIO 0
{-# NOINLINE nullHandle #-}

withOutput :: MonadUnliftIO m => Bool -> Handle -> (OutputHandle -> m a) -> m a
withOutput allowAnsi h f =
  askRunInIO >>= \runIO -> liftIO do
    buf <- newActionBufferIO 32
    Async.withAsync (runOutput allowAnsi h buf) \outputThread -> do
      -- Link the output thread to this thread: In the case that an exception
      -- is thrown in the output thread it will be rethrown here.
      Async.link outputThread
      runIO (f (OutputHandle buf)) `finally` do
        -- Send the termination signal and wait for the thread to complete. We
        -- explicitly ignore exceptions reported from the output thread because
        -- we are still linked to it which might lead to a double report.
        --
        -- Waiting for `outputThread` is required because otherwise it will get
        -- canceled once one return from the surrounding `withAsync`.
        --
        -- TODO: Doing this cleanup (action buffer termination + waiting) even
        -- in the exceptional case is debatable! However, there are at least
        -- some exceptional cases in the current design where we want the
        -- cleanup. So for now we will do cleanup regardless of why `f` exits.
        atomically (terminateActionBuffer buf)
        Async.waitCatch outputThread

outputStr :: MonadIO m => OutputHandle -> String -> m ()
outputStr b = outputS b . showString

outputStrLn :: MonadIO m => OutputHandle -> String -> m ()
outputStrLn b s = outputS b $ showString s . showChar '\n'

outputShow :: (MonadIO m, Show a) => OutputHandle -> a -> m ()
outputShow b = outputLnS b . shows

outputLnS :: MonadIO m => OutputHandle -> ShowS -> m ()
outputLnS h s = outputS h (s . showChar '\n')

outputS :: MonadIO m => OutputHandle -> ShowS -> m ()
outputS (OutputHandle buf) =
  liftIO . writeActionBuffer buf . WriteMessage

outputSticky :: MonadIO m => OutputHandle -> String -> m ()
outputSticky (OutputHandle buf) =
  liftIO . writeActionBuffer buf . SetSticky . Sticky

clearSticky :: MonadIO m => OutputHandle -> m ()
clearSticky h = outputSticky h ""

-- $sticky
--
-- A sticky message will stick to the bottom of the terminal: When other
-- messages are output via 'outputStr' or 'outputStrLn' the sitcky message will
-- be cleared and re-output below.
--
-- === Sticky Message Limitations ===
--
-- 1. Messages will only stick to the bottom of the screen for other
-- messages output via the same 'OutputHandle'.
--
-- 2. Sticky messages should be kept relatively short: if the terminal's width
-- broke a sticky message into multiple lines it would become impossible to
-- clear more than the last line resulting in the partial sticky message
-- remaining on screen.
--
-- 3. Support for sticky messages requires for the output device to support
-- ANSI escape sequences. If support for these is not detected sticky messages
-- will appear as if output as regular messages via 'outputStrLn'.

-- | A bounded buffer of output actions.
data ActionBuffer = ActionBuffer !Word !(TVar Word) !(TVar [Action])

pattern NullBuffer :: ActionBuffer
pattern NullBuffer <- ActionBuffer 0 _ _

newActionBufferIO :: Word -> IO ActionBuffer
newActionBufferIO !cap =
  ActionBuffer cap <$> newTVarIO cap <*> newTVarIO []

writeActionBuffer :: ActionBuffer -> Action -> IO ()
writeActionBuffer NullBuffer _ = pure ()
writeActionBuffer (ActionBuffer _ capVar actVar) a = atomically do
  cap <- readTVar capVar
  guard $ cap > 0
  writeTVar capVar $! cap - 1
  modifyTVar actVar (a :)

terminateActionBuffer :: ActionBuffer -> STM ()
terminateActionBuffer (ActionBuffer _ _ actVar) = do
  -- This should be the last write, do it unconditionally.
  modifyTVar actVar (Done :)

readActionBufferRev :: ActionBuffer -> STM (NonEmpty Action)
readActionBufferRev (ActionBuffer cap capVar actVar) = do
  actions <- readTVar actVar
  result <- case actions of
    [] -> retry
    a : as -> pure $ a :| as
  writeTVar actVar []
  writeTVar capVar cap
  pure result

interpretRev :: Sticky -> L.Fold Action (Sticky, ShowS, Bool)
interpretRev sticky0 =
  (,,)
    <$> mapMaybeL getSticky (fromMaybe sticky0 <$> L.head)
    <*> L.foldMap getMessage (appEndo . getDual)
    <*> L.any isDone
  where
    getSticky = \case
      SetSticky s -> Just s
      _ -> Nothing
    getMessage = \case
      WriteMessage s -> Dual (Endo s)
      _ -> mempty
    isDone = \case
      Done -> True
      _ -> False

mapMaybeL :: (a -> Maybe b) -> L.Fold b c -> L.Fold a c
mapMaybeL f (L.Fold step0 ini0 final0) = L.Fold step ini0 final0
  where
    step x = maybe x (step0 x) . f

data Action
  = SetSticky Sticky
  | WriteMessage ShowS
  | Done

runOutput :: Bool -> Handle -> ActionBuffer -> IO ()
runOutput allowAnsi h actBuffer = bracket prepare id (const run)
  where
    prepare :: IO (IO ())
    prepare = do
      -- We want a block buffered handle, we flush it at the end of each chunk
      -- of output.
      buf <- hGetBuffering h
      case buf of
        BlockBuffering _ ->
          -- Handle is already block buffered.
          pure (pure ())
        _ ->
          -- Make it block buffered, restore the previous buffering at the end.
          hSetBuffering h (BlockBuffering Nothing)
            $> hSetBuffering h buf

    run :: IO ()
    run = do
      -- Flush the handle once. Probably not really necessary but seems strange
      -- not to do it here.
      hFlush h
      -- Run the main loop.
      useAnsi <-
        (allowAnsi &&) . fromMaybe False
          <$> ANSI.hSupportsANSIWithoutEmulation h
      go useAnsi emptySticky

    clearCode :: Bool -> ShowS
    clearCode True =
      -- Clear the current line which contains the current sticky or is empty.
      showString ANSI.clearLineCode . showString (ANSI.setCursorColumnCode 0)
    clearCode False =
      -- ANSI is not supported: since stickies are interleaved with normal
      -- messages nothing has to be cleared.
      id

    go :: Bool -> Sticky -> IO ()
    go !ansi prevSticky = do
      -- Read the next batch.
      acts <- atomically $ readActionBufferRev actBuffer
      let noAnsiNoSticky
            | ansi = id
            | otherwise = mapMaybe \case
              -- Ignore empty stickies.
              SetSticky (Sticky "") -> Nothing
              -- Convert stickies to regular messages.
              SetSticky (Sticky s) -> Just $ WriteMessage $ showString s . showChar '\n'
              -- Keep everything else as-is.
              action -> Just action
      let (Sticky sticky, message, done) =
            toList acts
              & noAnsiNoSticky
              & L.fold (interpretRev prevSticky)
      -- Include a final newline if output is completed after this batch.
      let writtenSticky
            | done && not (null sticky) = sticky ++ "\n"
            | otherwise = sticky

      -- Write that batch to the output.
      hPutStr h $ clearCode ansi $ message writtenSticky
      hFlush h

      -- Continue with the next batch if we're not yet done.
      when (not done) $ go ansi $ Sticky sticky

data CounterState = CounterState
  { counterRunning :: !Int,
    counterFinished :: !Int,
    counterOverall :: !Int,
    counterTitle :: String
  }

data Counter = Counter !OutputHandle !(MVar CounterState)

{- ORMOLU_DISABLE -}
makeLenses ''CounterState
counterRunningL :: Lens' CounterState Int
counterFinishedL :: Lens' CounterState Int
counterOverallL :: Lens' CounterState Int
counterTitleL :: Lens' CounterState String
{- ORMOLU_ENABLE -}

-- | A 'CounterState' with all fields set to zero and an empty title.
zeroCounter :: CounterState
zeroCounter = CounterState 0 0 0 ""

-- | Creates a new counter starting from the given initial 'CounterState'.
newCounter :: MonadIO m => OutputHandle -> CounterState -> m Counter
newCounter handle !st = liftIO $ Counter handle <$> newMVar st

-- | Creates a new counter starting from 'zeroCounter'.
newZeroCounter :: MonadIO m => OutputHandle -> m Counter
newZeroCounter handle = newCounter handle zeroCounter

-- | Create a new counter starting from the given state and immediately output
-- the first message.
newCounterStart :: MonadIO m => OutputHandle -> CounterState -> m Counter
newCounterStart handle st = liftIO do
  cntr <- newCounter handle st
  cntr <$ outputCounter cntr st

renderCounter :: CounterState -> ShowS
renderCounter CounterState {..} =
  showChar '['
    . showPadded counterRunning
    . showChar '/'
    . showPadded counterFinished
    . showChar '/'
    . showPadded counterOverall
    . showChar ']'
    . if null counterTitle then id else showString (' ' : counterTitle)
  where
    maxlen =
      -- We assume that counters won't be negative.
      length . show $
        counterRunning `max` counterFinished `max` counterOverall
    showPadded n =
      let nlen = length $ show n
       in showString (replicate (maxlen - nlen) ' ') . shows n

outputCounter :: Counter -> CounterState -> IO ()
outputCounter (Counter handle _) st =
  outputSticky handle $ renderCounter st ""

counterUpdate :: MonadIO m => Counter -> (CounterState -> CounterState) -> m ()
counterUpdate cntr@(Counter _ stVar) f =
  liftIO $ modifyMVar_ stVar \st -> do
    let !st' = f st
    outputCounter cntr st'
    pure st'

counterDone :: MonadIO m => Counter -> m ()
counterDone (Counter handle _) = clearSticky handle

wrapCounter :: MonadIO m => Counter -> String -> m a -> m a
wrapCounter c title m = counterUpdate c start *> m <* counterUpdate c end
  where
    start = counterRunningL +~ 1 >>> counterTitleL .~ title
    end = counterRunningL -~ 1 >>> counterFinishedL +~ 1
