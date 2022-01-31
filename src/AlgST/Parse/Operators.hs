{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}

module AlgST.Parse.Operators
  ( OpSeq (..),
    OpsHead (..),
    Parenthesized (..),
    parseOperators,
  )
where

import AlgST.Parse.Phase
import qualified AlgST.Syntax.Expression as E
import AlgST.Syntax.Operators
import AlgST.Syntax.Variable
import AlgST.Util.ErrorMessage
import Control.Category ((>>>))
import Control.Monad
import Control.Monad.Validate
import qualified Data.DList as DL
import Data.Foldable
import qualified Data.Map.Strict as Map
import Syntax.Base

data OpsHead
  = OpsExp
  | OpsOp

data OpSeq first a where
  Nil :: OpSeq first a
  Operand :: PExp -> OpSeq OpsOp v -> OpSeq OpsExp v
  Operator :: v -> OpSeq OpsExp v -> OpSeq OpsOp v

deriving instance Functor (OpSeq first)

deriving instance Foldable (OpSeq first)

deriving instance Traversable (OpSeq first)

parseOperators ::
  MonadValidate [Diagnostic] m =>
  Parenthesized ->
  OpSeq first (ProgVar, [PType]) ->
  m PExp
parseOperators ps = resolveOperators >=> (groupOperators >>> foldGroupedOperators ps)

data Parenthesized
  = TopLevel
  | InParens
  deriving (Eq)

data OpGrouping = OpGrouping
  { leadingExpr :: Maybe PExp,
    opExprPairs :: [(ResolvedOp, PExp)],
    trailingOp :: Maybe ResolvedOp
  }

data ResolvedOp = ResolvedOp
  { -- | unparenthesized name
    operatorName :: ProgVar,
    operatorTyArgs :: [PType],
    operatorInfo :: Info
  }

instance Position ResolvedOp where
  pos = operatorName >>> pos

data Prec = MinPrec | Prec !Precedence | MaxPrec
  deriving (Eq, Ord, Show)

instance Bounded Prec where
  minBound = MinPrec
  maxBound = MaxPrec

foldGroupedOperators ::
  MonadValidate [Diagnostic] m => Parenthesized -> OpGrouping -> m PExp
foldGroupedOperators ps = \case
  OpGrouping Nothing [] Nothing ->
    error "internal parsing error: empty operator sequence"
  OpGrouping Nothing [] (Just op) ->
    refute [errorMissingBothOperands $ operatorName op]
  OpGrouping Nothing ((op, _) : _) Nothing
    | InParens <- ps -> refute [errorUnsupportedRightSection op]
    | otherwise -> refute [errorMissingOperand Left [] op]
  OpGrouping Nothing ((opL, _) : _) (Just opR) ->
    refute
      [ errorMissingOperand Left [] opL,
        errorMissingOperand Right [] opR
      ]
  OpGrouping (Just _) _ (Just op)
    | TopLevel <- ps ->
      let sectionHelp =
            [ ErrLine,
              Error
                "Wrap the whole expression in parentheses \
                \to partially apply the operator."
            ]
       in refute [errorMissingOperand Right sectionHelp op]
  -- Otherwise fall through to the next case.

  OpGrouping (Just e) ops mopr ->
    foldOperators e ops mopr

foldOperators ::
  forall m.
  MonadValidate [Diagnostic] m =>
  PExp ->
  [(ResolvedOp, PExp)] ->
  Maybe ResolvedOp ->
  m PExp
foldOperators e0 ops0 = \case
  Nothing ->
    -- Ordinary operator chain.
    --
    -- `go` will always consume all operator-operand pairs because every
    -- operator has a higher precedence than `minBound`. Therefore we can
    -- discard the second component.
    fst <$> go e0 minBound Nothing ops0
  Just secOp -> do
    -- Operator section.
    --
    -- We use the operator to the right as the starting precedence. Should `go`
    -- not consume all operator-operand pairs we emit an error. Such a section
    -- could be for example
    --
    --    (3 + 4 *)
    --
    -- We want to prohibit those. Although a possible desugaring would be
    --
    --    (*) (3+4)
    --
    -- this breaks very easily when adding the second argument for (*),
    -- leaving us with
    --
    --    (+) 3 ((*) 4 x)
    --
    -- which suddenly associates differently.
    (e, remainingOps) <- go e0 (nextPrec Left secOp) (Just secOp) ops0
    case remainingOps of
      [] ->
        -- All fine. Construct the final partial application.
        pure $ buildOpApplication secOp e Nothing
      (op, _) : _ ->
        refute . pure $
          PosError
            (pos secOp)
            [ Error "The operator",
              Error $ operatorName secOp,
              Error "of a section must have lower precedence",
              ErrLine,
              Error "        than",
              Error $ operatorName op,
              Error "at",
              Error $ pos op,
              ErrLine,
              Error "Use parentheses to explicitly specify the associativity of the operands."
            ]
  where
    -- The 'Side' specifies wether parsing continues on the left or the right
    -- of the operator.
    --
    -- If the operator associates for example to the left and parsing continues
    -- on the left we do not increase the precedence context.
    nextPrec :: Side -> ResolvedOp -> Prec
    nextPrec side op
      | assoc op /= NA && assoc op /= select side L R =
        if prec op == maxBound
          then MaxPrec
          else Prec $ succ $ prec op
      | otherwise =
        Prec $ prec op

    prec =
      operatorInfo >>> opPrec
    assoc =
      operatorInfo >>> opAssoc

    go ::
      PExp -> Prec -> Maybe ResolvedOp -> [(ResolvedOp, PExp)] -> m (PExp, [(ResolvedOp, PExp)])
    go lhs minPrec mprev ((op, rhs) : ops)
      | Just prevOp <- mprev,
        minPrec == Prec (prec op) && assoc prevOp == NA =
        refute [errorNonAssocOperators prevOp op]
      | minPrec <= Prec (prec op) = do
        (rhs', ops') <- go rhs (nextPrec Right op) (Just op) ops
        let res = buildOpApplication op lhs (Just rhs')
        go res minPrec (Just op) ops'
    go lhs _ _ ops =
      pure (lhs, ops)

buildOpApplication :: ResolvedOp -> PExp -> Maybe PExp -> PExp
buildOpApplication op lhs mrhs
  | UserNamed "<|" <- operatorName op,
    null (operatorTyArgs op),
    Just rhs <- mrhs =
    -- Desugar operator to direct function application.
    E.App (pos op) lhs rhs
  | UserNamed "|>" <- operatorName op,
    null (operatorTyArgs op),
    Just rhs <- mrhs =
    -- Desugar operator to (flipped) direct function application.
    E.App (pos op) rhs lhs
  | otherwise = do
    let opVar = E.Var (pos op) $ mkVar (pos op) $ opName $ operatorInfo op
    let opExp = E.foldTypeApps (const pos) opVar (operatorTyArgs op)
    let appLhs = E.App (pos lhs) opExp lhs
    maybe appLhs (E.App <$> pos <*> pure appLhs <*> id) mrhs

-- | Annotates all 'ProgVar's with their operator 'Info' or returns a list of
-- errors about unknown operators.
resolveOperators ::
  ( MonadValidate [Diagnostic] m,
    Traversable f
  ) =>
  f (ProgVar, [PType]) ->
  m (f ResolvedOp)
resolveOperators = traverse \(v, tys) ->
  case Map.lookup (intern v) knownOperators of
    Nothing ->
      refute [errorUnknownOperator v]
    Just i ->
      pure
        ResolvedOp
          { operatorName = v,
            operatorTyArgs = tys,
            operatorInfo = i
          }

groupOperators :: forall first. OpSeq first ResolvedOp -> OpGrouping
groupOperators = \case
  Nil -> OpGrouping Nothing [] Nothing
  Operand e ops -> go (Just e) mempty ops
  ops@Operator {} -> go Nothing mempty ops
  where
    go ::
      Maybe PExp ->
      DL.DList (ResolvedOp, PExp) ->
      OpSeq OpsOp ResolvedOp ->
      OpGrouping
    go mLhs groupedOps = \case
      Nil ->
        OpGrouping
          { leadingExpr = mLhs,
            opExprPairs = toList groupedOps,
            trailingOp = Nothing
          }
      Operator op Nil ->
        OpGrouping
          { leadingExpr = mLhs,
            opExprPairs = toList groupedOps,
            trailingOp = Just op
          }
      Operator op (Operand e ops) ->
        go mLhs (DL.snoc groupedOps (op, e)) ops

errorMissingBothOperands :: ProgVar -> Diagnostic
errorMissingBothOperands v =
  PosError
    (pos v)
    [ Error "Operator",
      Error v,
      Error "is missing its operands.",
      ErrLine,
      Error $ "Write it as ‘(" ++ show v ++ ")’ to use it as a function value."
    ]

errorMissingOperand ::
  -- | 'Left' or 'Right', whichever operand is missing.
  Side ->
  -- | Additional 'ErrorMessage' components
  [ErrorMessage] ->
  ResolvedOp ->
  Diagnostic
errorMissingOperand side additionalMsgs v = PosError (pos v) (msgs ++ additionalMsgs)
  where
    msgs =
      [ Error "Operator",
        Error $ operatorName v,
        Error $ "is missing its " ++ select side "left" "right" ++ " operand.",
        ErrLine,
        Error "Write it as",
        Error $ "‘(" ++ show (operatorName v) ++ ")’",
        Error "to use it as a function value."
      ]

type Side = forall a. a -> Either a a

select :: Side -> b -> b -> b
select side = either const (const id) . side

errorUnsupportedRightSection :: ResolvedOp -> Diagnostic
errorUnsupportedRightSection =
  errorMissingOperand
    Left
    [ ErrLine,
      Error "Right sections are not (yet) supported."
    ]

errorUnknownOperator :: ProgVar -> Diagnostic
errorUnknownOperator v =
  PosError
    (pos v)
    [ Error "Unknown operator",
      Error v
    ]

errorNonAssocOperators :: ResolvedOp -> ResolvedOp -> Diagnostic
errorNonAssocOperators v1 v2 =
  PosError
    (pos v2)
    [ Error "Non-associative operators",
      ErrLine,
      Error "   ",
      Error $ operatorName v1,
      Error "at",
      Error (pos v1),
      ErrLine,
      Error "and",
      Error $ operatorName v2,
      Error "at",
      Error (pos v2),
      ErrLine,
      Error "are used next to each other.",
      ErrLine,
      ErrLine,
      Error "Use parentheses to explicitly specify the associativity."
    ]
