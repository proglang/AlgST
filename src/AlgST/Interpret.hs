{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}

module AlgST.Interpret where

import AlgST.Parse.ParseUtils (pattern PairConId)
import AlgST.Syntax.Expression qualified as E
import AlgST.Syntax.Kind qualified as K
import AlgST.Syntax.Variable
import AlgST.Typing (Tc, TcBind, TcExp, TcExpX (..))
import AlgST.Util.Lenses
import Control.Concurrent
import Control.Monad.Reader
import Data.Bifunctor
import Data.Functor.Identity (Identity (runIdentity))
import Data.IORef
import Data.Map.Strict qualified as Map
import Data.Void
import GHC.IORef (atomicModifyIORef'_)
import Lens.Family2
import Syntax.Base (defaultPos)

type Env = Map.Map ProgVar Value

type ThreadList = [ThreadId]

data EvalSt = EvalSt
  { -- | The next channel id to be used. Examining this value at the end gives
    -- information about how many channels were created.
    stNextChannel :: !ChannelId,
    -- | A list of all threads forked during evaluation.
    --
    -- TODO: Think about exception propagation.
    stForked :: ThreadList
  }

-- | Evaluating requires an environment of bound identifiers. It collects a
-- list of created threads and keeps track of the next 'ChannelId'.
type EvalM = ReaderT (Env, IORef EvalSt) IO

type ChannelId = Int

data Channel = Channel
  { channelId :: !ChannelId,
    channelVar :: !(MVar Value)
  }

-- | An indicator to differentiate the two channel endpoints.
data Side = A | B
  deriving stock (Show)

data Value
  = -- | > Closure env var body
    --
    -- @env@ must be lazy to allow the entries to refer to the closure itself
    -- in recursive values.
    Closure Env !ProgVar !TcExp
  | -- | A fully applied constructor.
    --
    -- Pairs are represented as
    --
    -- > Con "(,)" [a, b]
    --
    -- The 'Pair' pattern synonym exists to help with matching on pairs.
    Con !String [Value]
  | -- | Endpoint to a channel. The 'Side' is an indicator for the user.
    Endpoint !Side !Channel
  | -- | Labels can't be constructed by the user. The are user to handle
    -- select/case operations on channels.
    Label !String
  | Number !Integer
  | String !String
  | Char !Char
  | Unit

pattern Pair :: Value -> Value -> Value
pattern Pair a b = Con PairConId [a, b]

instance Show Value where
  showsPrec p =
    paren . \case
      Closure env v e ->
        [ showString "Closure ",
          showsPrec 11 env,
          showString " ",
          showsPrec 11 v,
          showString " {",
          showsPrec 11 e,
          showString "}"
        ]
      Pair a b ->
        [ showString "Pair ",
          showsPrec 11 a,
          showString " ",
          showsPrec 11 b
        ]
      Con c vs ->
        [ showString "Con ",
          showsPrec 11 c,
          showString " ",
          showsPrec 11 vs
        ]
      Endpoint side c ->
        [ showString "Endpoint ",
          showsPrec 11 side,
          showString " ",
          showsPrec 11 (channelId c)
        ]
      Label lbl -> unary "Label" lbl
      Number n -> unary "Number" n
      String s -> unary "String" s
      Char c -> unary "Char" c
      Unit -> [showString "Unit"]
    where
      unary :: Show a => String -> a -> [ShowS]
      unary label a = [showString label . showChar ' ', showsPrec 11 a]
      paren :: [ShowS] -> ShowS
      paren [x] = x
      paren xs = showParen (p > 10) $ foldr (.) id xs

data Type a where
  TClosure :: Type (Env, ProgVar, TcExp)
  TCon :: Type (String, [Value])
  TChannel :: Type Channel
  TLabel :: Type String
  TNumber :: Type Integer
  TString :: Type String
  TChar :: Type Char
  TUnit :: Type ()

{- ORMOLU_DISABLE -}
makeLenses ''EvalSt
stNextChannelL :: Lens' EvalSt ChannelId
stForkedL :: Lens' EvalSt ThreadList
{- ORMOLU_ENABLE -}

evalLiteral :: E.Lit -> Value
evalLiteral = \case
  E.Unit -> Unit
  E.Int n -> Number n
  E.Char c -> Char c
  E.String s -> String s

eval :: TcExp -> EvalM Value
eval = \case
  E.Lit _ l -> do
    pure $ evalLiteral l
  E.Var _ v -> do
    lookupEnv "variable" v
  E.Con _ c -> do
    lookupEnv "constructor" c

  --
  E.Abs _ bind -> do
    (env, _) <- ask
    pure $ closure env bind

  --
  E.App _ e1 e2 -> do
    (env, var, body) <- evalAs TClosure e1
    arg <- eval e2
    let env' = Map.insert var arg env
    local (first $ const env') (eval body)

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
    (env, _) <- ask
    let env' = Map.insert v val env
        val = closure env' $ recBody rl
    pure val

  -- Creates a new channel and returns a pair of the two endpoints.
  E.New _ _ -> do
    c <- newChannel
    pure $ Pair (Endpoint A c) (Endpoint B c)

  -- Constructs a function which sends the selected constructor as a label.
  E.Select _ c -> do
    error "TODO: E.Select"

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
    (c, vs) <- unwrap TCon val
    let cvar = mkVar defaultPos c
    if
        | Just b <- Map.lookup cvar (E.casesPatterns cases) ->
          localBinds (zip (E.branchBinds b) vs) do
            eval $ E.branchExp b
        | Just b <- E.casesWildcard cases ->
          localBinds [(runIdentity (E.branchBinds b), val)] do
            eval $ E.branchExp b
        | otherwise ->
          unmatchableConstructor c

  --
  E.Exp (RecvCase _ e cases) -> do
    chanVal <- eval e
    channel <- unwrap TChannel chanVal
    l <- unwrap TLabel =<< readChannel channel
    b <-
      E.casesPatterns cases
        & Map.lookup (mkVar defaultPos l)
        & maybe (unmatchableConstructor l) pure
    localBinds [(runIdentity (E.branchBinds b), chanVal)] do
      eval $ E.branchExp b

newChannel :: EvalM Channel
newChannel = do
  (_, ref) <- ask
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
  env@(_, ref) <- ask
  -- Fork evaluation.
  tid <- liftIO $ forkIO do
    runReaderT (f =<< eval e) env
  -- Record the forked thread.
  void . liftIO $ atomicModifyIORef'_ ref \st ->
    st & stForkedL %~ (tid :)

recBody :: E.RecLam Tc -> E.Bind Tc
recBody (E.RecTermAbs _ bind) = bind
recBody (E.RecTypeAbs _ (K.Bind _ _ _ rl)) = recBody rl

closure :: Env -> TcBind -> Value
closure env (E.Bind _ _ v _ body) = Closure env v body

localBinds :: [(ProgVar, Value)] -> EvalM a -> EvalM a
localBinds binds = local $ first \e -> Map.fromList binds <> e

lookupEnv :: String -> ProgVar -> EvalM Value
lookupEnv kind v = maybe (fail err) pure =<< asks (Map.lookup v . fst)
  where
    err = unwords ["internal error:", kind, show v, "is not bound."]

evalAs :: Type a -> TcExp -> EvalM a
evalAs ty = eval >=> unwrap ty

unwrap :: Type a -> Value -> EvalM a
unwrap TNumber (Number n) = pure n
unwrap TString (String s) = pure s
unwrap TChar (Char c) = pure c
unwrap TUnit Unit = pure ()
unwrap TClosure (Closure env v e) = pure (env, v, e)
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
      TUnit -> "unit"
      TClosure -> "a closure"

unmatchableConstructor :: String -> EvalM a
unmatchableConstructor c =
  fail $ unwords ["internal error: unmatchable constructor", c]
{-# NOINLINE unmatchableConstructor #-}
