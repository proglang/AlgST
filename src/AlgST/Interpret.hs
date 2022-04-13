{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GADTs #-}

module AlgST.Interpret where

import AlgST.Syntax.Expression qualified as E
import AlgST.Syntax.Kind qualified as K
import AlgST.Syntax.Variable
import AlgST.Typing (Tc, TcBind, TcExp)
import Control.Monad.Reader
import Data.Map.Strict qualified as Map
import Data.Void

type Env = Map.Map ProgVar Value

type EvalM = Reader Env

data Value
  = -- | > Closure env var body
    --
    -- @env@ must be lazy to allow the entries to refer to the closure itself
    -- in recursive values.
    Closure Env !ProgVar !TcExp
  | Pair !Value !Value
  | Number !Integer
  | String !String
  | Char !Char
  | Unit

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
      Number n ->
        [showString "Number ", showsPrec 11 n]
      String s ->
        [showString "String ", showsPrec 11 s]
      Char c ->
        [showString "Char ", showsPrec 11 c]
      Unit ->
        [showString "Unit"]
    where
      paren [x] = x
      paren xs = showParen (p > 10) $ foldr (.) id xs

data Type a where
  TClosure :: Type (Env, ProgVar, TcExp)
  TNumber :: Type Integer
  TString :: Type String
  TChar :: Type Char
  TUnit :: Type ()

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
    asks $ lookupEnv "variable" v
  E.Con _ c -> do
    asks $ lookupEnv "constructor" c
  E.Abs _ bind -> do
    env <- ask
    pure $ closure env bind
  E.App _ e1 e2 -> do
    (env, var, body) <- unwrap TClosure <$> eval e1
    !arg <- eval e2
    let env' = Map.insert var arg env
    local (const env') (eval body)
  E.Pair _ e1 e2 -> do
    !v1 <- eval e1
    !v2 <- eval e2
    pure $ Pair v1 v2
  E.Cond x _ _ _ -> do
    absurd x
  E.Case x _ _ -> do
    absurd x
  E.TypeAbs _ (K.Bind _ _ _ e) -> do
    eval e
  E.TypeApp _ e _ -> do
    eval e
  E.UnLet x _ _ _ _ -> do
    absurd x
  E.PatLet x _ _ _ _ -> do
    absurd x
  E.Rec _ v _ rl -> do
    -- Like a lambda abstraction but `v` is bound in the body.
    --
    -- TODO: Ensure that the shadowing rules between the interpreter and type
    -- checker are consistent when `arg` and `v` are the same.
    env <- ask
    let env' = Map.insert v val env
        val = closure env' $ recBody rl
    pure val
  E.New _ ty -> do
    error "E.New not yet implemented"
  E.Select _ pv -> do
    error "E.Select not yet implemented"
  E.Fork _ exp -> do
    error "E.Fork not yet implemented"
  E.Fork_ _ exp -> do
    error "E.Fork_ not yet implemented"
  E.Exp xe -> do
    error "E.Exp not yet implemented"

recBody :: E.RecLam Tc -> E.Bind Tc
recBody (E.RecTermAbs _ bind) = bind
recBody (E.RecTypeAbs _ (K.Bind _ _ _ rl)) = recBody rl

closure :: Env -> TcBind -> Value
closure env (E.Bind _ _ v _ body) = Closure env v body

lookupEnv :: String -> ProgVar -> Env -> Value
lookupEnv kind v env = case Map.lookup v env of
  Just value -> value
  Nothing ->
    error . unwords $
      [ "internal error:",
        kind,
        show v,
        "is not bound."
      ]

unwrap :: Type a -> Value -> a
unwrap TNumber (Number n) = n
unwrap TString (String s) = s
unwrap TChar (Char c) = c
unwrap TUnit Unit = ()
unwrap TClosure (Closure env v e) = (env, v, e)
unwrap ty v =
  error . unwords $
    [ "internal error: expected",
      tyname,
      "but the value is\n\t",
      show v
    ]
  where
    tyname = case ty of
      TNumber -> "a number"
      TString -> "a string"
      TChar -> "a char"
      TUnit -> "unit"
      TClosure -> "a closure"
