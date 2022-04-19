{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}

module AlgST.Interpret
  ( EvalM,
    etaEvalM,
    runEval,
    runEvalWith,
    Settings (..),
    defaultSettings,
    InterpretError (..),
    EvalSt (..),
    ThreadList,
    ChannelId,
    Env,
    Value (..),
    Side (..),
    pattern Pair,
    eval,
    programEnvironment,
  )
where

import AlgST.Builtins
import AlgST.Parse.ParseUtils (pairConId, pattern PairConId)
import AlgST.Syntax.Decl
import AlgST.Syntax.Expression qualified as E
import AlgST.Syntax.Kind qualified as K
import AlgST.Syntax.Program
import AlgST.Syntax.Variable
import AlgST.Typing.Phase (Tc, TcBind, TcExp, TcExpX (..), TcProgram)
import AlgST.Util.Lenses
import Control.Concurrent
import Control.Concurrent.Async
import Control.Exception
import Control.Monad.Eta
import Control.Monad.Reader
import Data.DList qualified as DL
import Data.Foldable
import Data.Functor.Identity (Identity (runIdentity))
import Data.Hashable
import Data.IORef
import Data.List qualified as List
import Data.Map.Lazy qualified as LMap
import Data.Map.Strict qualified as Map
import Data.Monoid
import Data.Void
import GHC.Stack
import Lens.Family2
import Syntax.Base (defaultPos)
import System.Console.ANSI
import Prelude hiding (log)

-- | The environment associates names with either an unevaluated expression or
-- a final value.
--
-- Unevaluted expressions are used for top-level definitions. They are not
-- updated after evaluation.
--
-- FIXME: Caching of global values seems reasonable.
type Env = Map.Map ProgVar (Either TcExp Value)

-- | A list of spawned threads.
type ThreadList = [Async ()]

newtype Settings = Settings
  { evalDebugMessages :: Bool
  }

defaultSettings :: Settings
defaultSettings =
  Settings
    { evalDebugMessages = False
    }

data EvalInfo = EvalInfo
  { evalEnv :: !Env,
    evalState :: !(IORef EvalSt),
    evalSettings :: !Settings
  }

data EvalSt = EvalSt
  { -- | The next channel id to be used.
    stNextChannel :: !ChannelId,
    -- | The list of threads forked during evaluation. Accumulated to be able
    -- to wait for all to complete or to cancel them.
    --
    -- TODO: Think about exception propagation.
    stForked :: ThreadList
  }

newtype EvalM a = EvalM {unEvalM :: ReaderT EvalInfo IO a}
  deriving (Semigroup, Monoid) via (Ap EvalM a)
  deriving newtype (Functor, Applicative, Monad, MonadIO, MonadFix, MonadFail)

data InterpretError = InterpretError !CallStack !Pos String

instance Show InterpretError where
  -- Ideally we would derive 'Show' (display the representation) and keep
  -- 'displayException' as the user-level textual output.
  --
  -- But the test suite, which is were most of these should crop up if at all,
  -- does not use 'displayException' but delegates to 'show'.
  show = displayException

instance Exception InterpretError where
  displayException (InterpretError cs p e) =
    concat
      [ if p == defaultPos then "" else shows p ":",
        "interpret error: ",
        e,
        "\n\n",
        prettyCallStack cs
      ]

failInterpet :: HasCallStack => Pos -> String -> EvalM a
failInterpet !p = liftIO . throwIO . InterpretError callStack p

debugLogM :: String -> EvalM ()
debugLogM msg = do
  settings <- EvalM $ asks evalSettings
  debugLog settings msg

debugLog :: MonadIO m => Settings -> String -> m ()
debugLog Settings {evalDebugMessages = False} _ = pure ()
debugLog _ msg = liftIO do
  tid <- myThreadId
  let color =
        SetPaletteColor Foreground . fromIntegral $
          (hash tid + 3) `rem` (228 - 21) + 21
  putStrLn . concat $
    [ setSGRCode [color],
      "[",
      show tid,
      "] ",
      msg,
      setSGRCode [Reset]
    ]

runEval :: Env -> EvalM a -> IO a
runEval = runEvalWith defaultSettings

runEvalWith :: Settings -> Env -> EvalM a -> IO a
runEvalWith settings env (EvalM m) = do
  let st0 =
        EvalSt
          { stNextChannel = ChannelId 0,
            stForked = []
          }
  let allThreads f ref = do
        -- While waiting for threads new threads might spawn.
        ts <- atomicModifyIORef' ref \st ->
          ( st {stForked = []},
            stForked st
          )
        case ts of
          [] -> pure ()
          _ -> traverse_ f ts *> allThreads f ref
  let info ref =
        EvalInfo
          { evalEnv = env,
            evalState = ref,
            evalSettings = settings
          }
  let main ref =
        runReaderT
          ( m
              <* liftIO (allThreads wait ref)
              <* debugLog settings "Evaluation Completed"
          )
          (info ref)
  let failed ref =
        debugLog settings "Evaluation Failed"
          *> allThreads cancel ref
  debugLog settings "Beginning Evaluation"
  bracketOnError (newIORef st0) failed main

newtype ChannelId = ChannelId Word
  deriving stock (Show, Eq, Ord)

_ChannelId :: Lens' ChannelId Word
_ChannelId = coerced

data Channel = Channel
  { channelId :: !ChannelId,
    channelSide :: !Side,
    -- | Filled by the sender, emptied by the receiving side.
    channelVar :: !(MVar Value),
    -- | Filled by the receiving side, emptied by the sender to synchronize the
    -- two endpoints.
    --
    -- To avoid deadlocks the operation on 'channelSync' should always happen
    -- after the operation on 'channelVar'.
    channelSync :: !(MVar ())
  }

instance Show Channel where
  show c = show (channelId c ^. _ChannelId) ++ "." ++ show (channelSide c)

-- | An indicator to differentiate the two channel endpoints.
data Side = A | B
  deriving stock (Show)

data Value
  = -- | The 'String' is a description of the closure value used in the 'Show' instance.
    Closure String (Pos -> Value -> EvalM Value)
  | -- | A fully applied constructor. This includes pairs. See the 'Pair'
    -- pattern synonym for more information about their representation.
    Con !ProgVar [Value]
  | -- | Endpoint to a channel. The 'Side' is an indicator for the user.
    Endpoint !Channel
  | -- | Labels can't be constructed by the user. The are user to handle
    -- select/case operations on channels.
    Label !ProgVar
  | Number !Integer
  | String !String
  | Char !Char
  | Unit

-- | Pairs are represented through the 'Con' constructor with a name of 'PairConId'.
pattern Pair :: Value -> Value -> Value
pattern Pair a b <-
  Con (UserNamed PairConId) [a, b]
  where
    Pair a b = Con (pairConId defaultPos) [a, b]

instance Show Value where
  showsPrec p =
    parenWords . \case
      Closure s _ ->
        [ showString "Closure",
          showChar '{' . showString s . showChar '}'
        ]
      Pair a b ->
        [ showString "Pair",
          showsPrec 11 a,
          showsPrec 11 b
        ]
      Con c vs ->
        [ showString "Con",
          showsPrec 11 c,
          showsPrec 11 vs
        ]
      Endpoint c ->
        [ showString "Endpoint",
          showsPrec 11 (channelId c),
          showsPrec 11 (channelSide c)
        ]
      Label lbl -> unary "Label" lbl
      Number n -> unary "Number" n
      String s -> unary "String" s
      Char c -> unary "Char" c
      Unit -> [showString "Unit"]
    where
      unary :: Show a => String -> a -> [ShowS]
      unary label a = [showString label, showsPrec 11 a]
      parenWords :: [ShowS] -> ShowS
      parenWords [x] = x
      parenWords xs =
        List.intersperse (showChar ' ') xs
          & foldr (.) id
          & showParen (p > 10)

data Type a where
  TClosure :: Type (Pos -> Value -> EvalM Value)
  TCon :: Type (ProgVar, [Value])
  TChannel :: Type Channel
  TLabel :: Type ProgVar
  TNumber :: Type Integer
  TString :: Type String
  TChar :: Type Char

{- ORMOLU_DISABLE -}
makeLenses ''EvalSt
stNextChannelL :: Lens' EvalSt ChannelId
stForkedL :: Lens' EvalSt ThreadList
{- ORMOLU_ENABLE -}

{- ORMOLU_DISABLE -}
makeLenses ['evalEnv] ''EvalInfo
evalEnvL :: Lens' EvalInfo Env
{- ORMOLU_ENABLE -}

etaEvalM :: EvalM a -> EvalM a
etaEvalM (EvalM m) = EvalM (etaReaderT m)
{-# INLINE etaEvalM #-}

askEnv :: EvalM Env
askEnv = EvalM (asks evalEnv)
{-# INLINE askEnv #-}

localEnv :: (Env -> Env) -> EvalM a -> EvalM a
localEnv f = EvalM . local (evalEnvL %~ f) . unEvalM
{-# INLINE localEnv #-}

askState :: EvalM (IORef EvalSt)
askState = EvalM (asks evalState)
{-# INLINE askState #-}

modifyState :: (EvalSt -> EvalSt) -> EvalM ()
modifyState f = do
  ref <- askState
  liftIO $ atomicModifyIORef' ref \st -> (f st, ())
{-# INLINE modifyState #-}

-- | Constructs the global 'Env' from a type checked 'Program'.
programEnvironment :: TcProgram -> Env
programEnvironment p =
  LMap.mapMaybeWithKey (\k -> either (conValue k) (globValue k)) (programValues p)
    <> builtinsEnv
  where
    conValue :: ProgVar -> ConstructorDecl Tc -> Maybe (Either TcExp Value)
    conValue !name = \case
      DataCon _ _ _ _ args ->
        -- Data constructors correspond to closures evaluating to a 'Con' value.
        --
        -- We could easily build a 'TcExp' value for the constructors but their
        -- 'Value' representation is simple enough (and does not require the
        -- full environment) to construct the 'Value' directly.
        --
        -- TODO: 'buildDataConType' in AlgST.Typing does basically the same. A
        -- unification of the logic in one place might be reasonable.
        let go :: tcType -> (Int -> DL.DList Value -> Value) -> Int -> DL.DList Value -> Value
            go _ f remaining vs =
              Closure
                (show remaining ++ "*" ++ show (Con name (DL.toList vs)))
                (\_ v -> pure $ f (remaining - 1) (vs `DL.snoc` v))
         in Just $ Right $ foldr go (\_ -> Con name . DL.toList) args (length args) DL.empty
      ProtocolCon {} ->
        -- Protocol constructors can't appear as values after type checking.
        Nothing

    globValue :: ProgVar -> ValueDecl Tc -> Maybe (Either TcExp Value)
    globValue _ !d =
      -- The bodies of 'ValueDecl's (after TC) already contain the parameter
      -- lambda abstractions.
      Just . Left $ valueBody d

builtinsEnv :: Env
builtinsEnv =
  Map.fromList
    [ bin "(+)" TNumber TNumber \x y -> Number (x + y),
      bin "(-)" TNumber TNumber \x y -> Number (x - y),
      bin "(*)" TNumber TNumber \x y -> Number (x * y),
      bin "(/)" TNumber TNumber \x y -> Number (x `div` y),
      bin "(%)" TNumber TNumber \x y -> Number (x `rem` y),
      bin "(<=)" TNumber TNumber \x y ->
        if x <= y
          then Con conTrue []
          else Con conFalse [],
      bin' "send" \(_, val) (p, channel) ->
        do
          c <- unwrap p TChannel channel
          putChannel c val
          pure channel,
      unary "receive" \p channel -> do
        c <- unwrap p TChannel channel
        v <- readChannel c
        pure $ Pair v channel
    ]
  where
    unary name f =
      (mkVar defaultPos name, Right $ Closure name f)
    bin' name f =
      unary name \p1 a ->
        pure $ Closure (name ++ " " ++ show a) (curry (f (p1, a)))
    bin name t1 t2 f =
      bin' name \(p1, a) (p2, b) -> do
        a' <- unwrap p1 t1 a
        b' <- unwrap p2 t2 b
        pure $ f a' b'

evalLiteral :: E.Lit -> Value
evalLiteral = \case
  E.Unit -> Unit
  E.Int n -> Number n
  E.Char c -> Char c
  E.String s -> String s

eval :: TcExp -> EvalM Value
eval =
  etaEvalM . \case
    E.Lit _ l -> do
      pure $ evalLiteral l
    E.Var p v -> do
      lookupEnv p v
    E.Con p c -> do
      lookupEnv p c

    --
    E.Abs _ bind -> do
      env <- askEnv
      pure $ closure env bind

    --
    E.App _ e1 e2 -> do
      f <- evalAs TClosure e1
      x <- eval e2
      f (pos e2) x

    --
    E.Pair _ e1 e2 -> do
      v1 <- eval e1
      v2 <- eval e2
      pure $ Pair v1 v2

    --
    E.Cond x _ _ _ -> do
      absurd x
    E.Case x _ _ -> do
      absurd x

    --
    E.TypeAbs _ (K.Bind _ _ _ e) -> do
      eval e
    E.TypeApp _ e _ -> do
      eval e

    --
    E.UnLet x _ _ _ _ -> do
      absurd x
    E.PatLet x _ _ _ _ -> do
      absurd x

    --
    E.Rec _ v _ rl -> do
      -- Like a lambda abstraction but `v` is bound in the body.
      env <- askEnv
      let env' = Map.insert v (Right val) env
          val = closure env' $ recBody rl
      pure val

    -- Creates a new channel and returns a pair of the two endpoints.
    E.New _ _ -> do
      (c1, c2) <- newChannel
      pure $ Pair (Endpoint c1) (Endpoint c2)

    -- Constructs a function which sends the selected constructor as a label.
    -- The type abstractions are skipped as they correspond to no-ops anyways.
    E.Select _ con -> do
      pure $ Closure ("\\c -> select " ++ show con ++ " c") \appPos c -> do
        chan <- unwrap appPos TChannel c
        putChannel chan $ Label con
        pure c

    -- Forks the evaluation of `e` and sends the result over a new channel. In
    -- the current thread it evaluates to that new channel.
    E.Fork _ e -> do
      (c1, c2) <- newChannel
      forkEval e (putChannel c2)
      pure $ Endpoint c1

    -- Forks the evaluation of `e` and returns `Unit` in the current thread.
    E.Fork_ _ e -> do
      forkEval e \_ -> pure ()
      pure Unit

    --
    E.Exp (ValueCase p e cases) -> do
      val <- eval e
      if
          | Con con vs <- val,
            Just b <- Map.lookup con (E.casesPatterns cases) ->
            -- Bind the payload values.
            evalBranch b vs
          | Just b <- E.casesWildcard cases ->
            -- We have to allow any value to appear as the scrutinee in a case
            -- expression since `let` is desugared this way.
            --
            -- Bind the scrutinee itself.
            evalBranch b [val]
          | otherwise ->
            -- Something went wrong somewhere.
            failInterpet p $ "unmatchable value " ++ show val

    --
    E.Exp (RecvCase p e cases) -> do
      chanVal <- eval e
      channel <- unwrap (pos e) TChannel chanVal
      l <- unwrap defaultPos TLabel =<< readChannel channel
      b <-
        E.casesPatterns cases
          & Map.lookup l
          & maybe (unmatchableConstructor p l) pure
      localBinds [(runIdentity (E.branchBinds b), chanVal)] do
        eval $ E.branchExp b

evalBranch :: Foldable f => E.CaseBranch f Tc -> [Value] -> EvalM Value
evalBranch b vs =
  localBinds (zip (toList (E.branchBinds b)) vs) do
    eval $ E.branchExp b

newChannel :: EvalM (Channel, Channel)
newChannel = do
  ref <- askState
  cid <- liftIO $ atomicModifyIORef' ref \st ->
    ( st & stNextChannelL . _ChannelId +~ 1,
      st ^. stNextChannelL
    )
  v1 <- liftIO newEmptyMVar
  v2 <- liftIO newEmptyMVar
  pure (Channel cid A v1 v2, Channel cid B v1 v2)

putChannel :: Channel -> Value -> EvalM ()
putChannel c v = do
  debugLogM $ "╔ send@" ++ show c ++ ": " ++ show v
  liftIO $ putMVar (channelVar c) v
  liftIO $ takeMVar (channelSync c)
  debugLogM $ "╚ send@" ++ show c

readChannel :: Channel -> EvalM Value
readChannel c = do
  debugLogM $ "╭ recv@" ++ show c
  v <- liftIO $ takeMVar (channelVar c)
  liftIO $ putMVar (channelSync c) ()
  debugLogM $ "╰ recv@" ++ show c ++ ": " ++ show v
  pure v

forkEval :: TcExp -> (Value -> EvalM ()) -> EvalM ()
forkEval e f = do
  env <- EvalM ask
  -- Fork evaluation.
  thread <- liftIO . mask_ $ asyncWithUnmask \restore -> do
    debugLog (evalSettings env) "┏ starting"
    restore (runReaderT (unEvalM (f =<< eval e)) env) `catch` \(e :: SomeException) -> do
      debugLog (evalSettings env) $ "┗ failed: " ++ displayException e
      throwIO e
    debugLog (evalSettings env) "┗ completed"
  -- Record the forked thread.
  modifyState \st -> do
    st & stForkedL %~ (thread :)

recBody :: E.RecLam Tc -> E.Bind Tc
recBody (E.RecTermAbs _ bind) = bind
recBody (E.RecTypeAbs _ (K.Bind _ _ _ rl)) = recBody rl

closure :: Env -> TcBind -> Value
closure env bind@(E.Bind _ _ v _ body) =
  Closure (show bind) \_ a -> do
    let env' = Map.insert v (Right a) env
    localEnv (const env') $ eval body

-- Establish a set of bindings locally.
localBinds :: [(ProgVar, Value)] -> EvalM a -> EvalM a
localBinds binds = localEnv \e -> Right `fmap` Map.fromList binds <> e

-- | Looks for the given variable in the current environment. If it resovles to
-- a top-level expression it will be evaluated before returning.
lookupEnv :: HasCallStack => Pos -> ProgVar -> EvalM Value
lookupEnv p v =
  askEnv
    >>= maybe (failInterpet p err) pure . Map.lookup v
    >>= either eval pure
  where
    err = show v ++ " is not bound."

-- | Evaluates the given expression and extracts the expected type.
evalAs :: Type a -> TcExp -> EvalM a
evalAs ty e = eval e >>= unwrap (pos e) ty

-- | Tries to extract the payload of the given type from a value. If the value
-- has a different type an 'InterpretError' will be thrown.
unwrap :: Pos -> Type a -> Value -> EvalM a
unwrap _ TNumber (Number n) = pure n
unwrap _ TString (String s) = pure s
unwrap _ TChar (Char c) = pure c
unwrap _ TClosure (Closure _ f) = pure f
unwrap _ TCon (Con c vs) = pure (c, vs)
unwrap _ TLabel (Label l) = pure l
unwrap _ TChannel (Endpoint c) = pure c
unwrap p ty v =
  failInterpet p . unwords $
    [ "expected",
      tyname,
      "but the value is\n\t",
      show v
    ]
  where
    tyname = case ty of
      TCon -> "a data value"
      TChannel -> "a channel"
      TLabel -> "a label"
      TNumber -> "a number"
      TString -> "a string"
      TChar -> "a char"
      TClosure -> "a closure"

unmatchableConstructor :: Pos -> ProgVar -> EvalM a
unmatchableConstructor p c = failInterpet p $ "unmatchable constructor " ++ show c
{-# NOINLINE unmatchableConstructor #-}
