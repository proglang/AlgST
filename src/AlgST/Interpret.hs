{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}

module AlgST.Interpret
  ( EvalM,
    etaEvalM,
    runEvalM,
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
import Data.Bifunctor
import Data.DList qualified as DL
import Data.Foldable
import Data.Functor.Identity (Identity (runIdentity))
import Data.IORef
import Data.List qualified as List
import Data.Map.Lazy qualified as LMap
import Data.Map.Strict qualified as Map
import Data.Void
import Lens.Family2
import Syntax.Base (defaultPos)

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

data EvalSt = EvalSt
  { -- | The next channel id to be used.
    stNextChannel :: !ChannelId,
    -- | The list of threads forked during evaluation. Accumulated to be able
    -- to wait for all to complete or to cancel them.
    --
    -- TODO: Think about exception propagation.
    stForked :: ThreadList
  }

newtype EvalM a = EvalM {unEvalM :: ReaderT (Env, IORef EvalSt) IO a}
  deriving newtype (Functor, Applicative, Monad, MonadIO, MonadFix, MonadFail)

runEvalM :: Env -> EvalM a -> IO a
runEvalM env (EvalM m) = do
  let st0 =
        EvalSt
          { stNextChannel = 0,
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
  bracketOnError (newIORef st0) (allThreads cancel) \ref ->
    runReaderT m (env, ref) <* allThreads wait ref

etaEvalM :: EvalM a -> EvalM a
etaEvalM (EvalM m) = EvalM (etaReaderT m)
{-# INLINE etaEvalM #-}

askEnv :: EvalM Env
askEnv = EvalM (asks fst)
{-# INLINE askEnv #-}

localEnv :: (Env -> Env) -> EvalM a -> EvalM a
localEnv f = EvalM . local (first f) . unEvalM
{-# INLINE localEnv #-}

askState :: EvalM (IORef EvalSt)
askState = EvalM (asks snd)
{-# INLINE askState #-}

modifyState :: (EvalSt -> EvalSt) -> EvalM ()
modifyState f = do
  ref <- askState
  liftIO $ atomicModifyIORef' ref \st -> (f st, ())
{-# INLINE modifyState #-}

type ChannelId = Word

data Channel = Channel
  { channelId :: !ChannelId,
    channelVar :: !(MVar Value)
  }

-- | An indicator to differentiate the two channel endpoints.
data Side = A | B
  deriving stock (Show)

data Value
  = -- | The 'String' is a description of the closure value used in the 'Show' instance.
    Closure String (Value -> EvalM Value)
  | -- | A fully applied constructor. This includes pairs. See the 'Pair'
    -- pattern synonym for more information about their representation.
    Con !ProgVar [Value]
  | -- | Endpoint to a channel. The 'Side' is an indicator for the user.
    Endpoint !Side !Channel
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
      Endpoint side c ->
        [ showString "Endpoint",
          showsPrec 11 side,
          showsPrec 11 (channelId c)
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
  TClosure :: Type (Value -> EvalM Value)
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

-- | Constrcuts the global 'Env' from a type checked 'Program'.
programEnvironment :: TcProgram -> Env
programEnvironment p =
  LMap.mapMaybeWithKey (\k -> either (conValue k) (globValue k)) (programValues p)
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
                (\v -> pure $ f (remaining - 1) (vs `DL.snoc` v))
         in Just $ Right $ foldr go (\_ -> Con name . DL.toList) args (length args) DL.empty
      ProtocolCon {} ->
        -- Protocol constructors can't appear as values after type checking.
        Nothing

    globValue :: ProgVar -> ValueDecl Tc -> Maybe (Either TcExp Value)
    globValue _ !d =
      -- The bodies of 'ValueDecl's (after TC) already contain the parameter
      -- lambda abstractions.
      Just . Left $ valueBody d

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
    E.Var _ v -> do
      lookupEnv v
    E.Con _ c -> do
      lookupEnv c

    --
    E.Abs _ bind -> do
      env <- askEnv
      pure $ closure env bind

    --
    E.App _ e1 e2 -> do
      f <- evalAs TClosure e1
      x <- eval e2
      f x

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
      --
      -- TODO: Ensure that the shadowing rules between the interpreter and type
      -- checker are consistent when `arg` and `v` are the same.
      env <- askEnv
      let env' = Map.insert v (Right val) env
          val = closure env' $ recBody rl
      pure val

    -- Creates a new channel and returns a pair of the two endpoints.
    E.New _ _ -> do
      c <- newChannel
      pure $ Pair (Endpoint A c) (Endpoint B c)

    -- Constructs a function which sends the selected constructor as a label.
    -- The type abstractions are skipped as they correspond to no-ops anyways.
    E.Select _ con -> do
      pure $ Closure ("\\c -> select " ++ show con ++ " c") \c -> do
        chan <- unwrap TChannel c
        putChannel chan $ Label con
        pure c

    -- Forks the evaluation of `e` and sends the result over a new channel. In
    -- the current thread it evaluates to that new channel.
    E.Fork _ e -> do
      c <- newChannel
      forkEval e (putChannel c)
      pure $ Endpoint A c

    -- Forks the evaluation of `e` and returns `Unit` in the current thread.
    E.Fork_ _ e -> do
      forkEval e \_ -> pure ()
      pure Unit

    --
    E.Exp (ValueCase _ e cases) -> do
      val <- eval e
      (con, vs) <- unwrap TCon val
      if
          | Just b <- Map.lookup con (E.casesPatterns cases) -> do
            localBinds (zip (E.branchBinds b) vs) do
              eval $ E.branchExp b
          | Just b <- E.casesWildcard cases ->
            localBinds [(runIdentity (E.branchBinds b), val)] do
              eval $ E.branchExp b
          | otherwise ->
            unmatchableConstructor con

    --
    E.Exp (RecvCase _ e cases) -> do
      chanVal <- eval e
      channel <- unwrap TChannel chanVal
      l <- unwrap TLabel =<< readChannel channel
      b <-
        E.casesPatterns cases
          & Map.lookup l
          & maybe (unmatchableConstructor l) pure
      localBinds [(runIdentity (E.branchBinds b), chanVal)] do
        eval $ E.branchExp b

newChannel :: EvalM Channel
newChannel = do
  ref <- askState
  cid <- liftIO $ atomicModifyIORef' ref \st ->
    ( st & stNextChannelL +~ 1,
      st ^. stNextChannelL
    )
  var <- liftIO newEmptyMVar
  pure $ Channel cid var

putChannel :: Channel -> Value -> EvalM ()
putChannel c = liftIO . putMVar (channelVar c)

readChannel :: Channel -> EvalM Value
readChannel = liftIO . takeMVar . channelVar

forkEval :: TcExp -> (Value -> EvalM ()) -> EvalM ()
forkEval e f = do
  env <- EvalM ask
  -- Fork evaluation.
  thread <- liftIO $ async do
    runReaderT (unEvalM (f =<< eval e)) env
  -- Record the forked thread.
  modifyState \st -> do
    st & stForkedL %~ (thread :)

recBody :: E.RecLam Tc -> E.Bind Tc
recBody (E.RecTermAbs _ bind) = bind
recBody (E.RecTypeAbs _ (K.Bind _ _ _ rl)) = recBody rl

closure :: Env -> TcBind -> Value
closure env bind@(E.Bind _ _ v _ body) =
  Closure (show bind) \a -> do
    let env' = Map.insert v (Right a) env
    localEnv (const env') $ eval body

-- Establish a set of bindings locally.
localBinds :: [(ProgVar, Value)] -> EvalM a -> EvalM a
localBinds binds = localEnv \e -> Right `fmap` Map.fromList binds <> e

-- | Looks for the given variable in the current environment. If it resovles to
-- a top-level expression it will be evaluated before returning.
lookupEnv :: ProgVar -> EvalM Value
lookupEnv v =
  askEnv
    >>= maybe (fail err) pure . Map.lookup v
    >>= either eval pure
  where
    err = unwords ["internal error:", show v, "is not bound."]

-- | Evaluates the given expression and extracts the expected type.
evalAs :: Type a -> TcExp -> EvalM a
evalAs ty = eval >=> unwrap ty

-- | Tries to extract the payload of the given type from a value. If the value
-- has a different type 'fail' will be called.
unwrap :: Type a -> Value -> EvalM a
unwrap TNumber (Number n) = pure n
unwrap TString (String s) = pure s
unwrap TChar (Char c) = pure c
unwrap TClosure (Closure _ f) = pure f
unwrap TCon (Con c vs) = pure (c, vs)
unwrap TLabel (Label l) = pure l
unwrap TChannel (Endpoint _ c) = pure c
unwrap ty v =
  fail . unwords $
    [ "internal error: expected",
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

unmatchableConstructor :: ProgVar -> EvalM a
unmatchableConstructor c =
  fail $ unwords ["internal error: unmatchable constructor", show c]
{-# NOINLINE unmatchableConstructor #-}
