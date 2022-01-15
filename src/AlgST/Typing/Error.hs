{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}

module AlgST.Typing.Error where

import AlgST.Parse.Unparser
import AlgST.Rename
import AlgST.Syntax.Decl
import qualified AlgST.Syntax.Expression as E
import qualified AlgST.Syntax.Kind as K
import qualified AlgST.Syntax.Type as T
import AlgST.Syntax.Variable
import qualified AlgST.Typing.Equality as Eq
import AlgST.Typing.Monad
import AlgST.Typing.Phase
import AlgST.Util
import AlgST.Util.ErrorMessage
import qualified Data.List as List
import Data.List.NonEmpty (NonEmpty, nonEmpty)
import qualified Data.List.NonEmpty as NE
import Syntax.Base hiding (Variable)
import Prelude hiding (truncate)

unexpectedKind ::
  (T.ForallX Position x, Unparse (T.XType x)) =>
  T.Type x ->
  K.Kind ->
  [K.Kind] ->
  PosError
unexpectedKind t kind hintKinds = PosError (pos t) (message ++ hint)
  where
    message =
      [ Error "Unexpected kind",
        Error kind,
        Error "for type",
        Error t
      ]

    hint = case nonEmpty hintKinds of
      Just hints ->
        [ErrLine, Error $ "Expected a subkind of " ++ joinOr (show <$> hints)]
      Nothing ->
        []
{-# NOINLINE unexpectedKind #-}

typeMismatch :: TcExp -> TcType -> TcType -> TcType -> TcType -> PosError
typeMismatch expr tyActual tyActualNF tyExpected tyExpectedNF =
  PosError (pos expr) $
    errUnline
      [ [Error "Expression"],
        [indent, Error expr],
        [Error "has type"],
        showType tyActual (Just tyActualNF),
        [Error "but it should have type"],
        showType tyExpected (Just tyExpectedNF)
      ]
{-# NOINLINE typeMismatch #-}

expectedBool :: Pos -> TcType -> PosError
expectedBool p ty =
  PosError
    p
    [ Error "Cannot match type of expression",
      ErrLine,
      Error "  ",
      Error ty,
      ErrLine,
      Error "with expected type",
      ErrLine,
      Error "  ",
      Error $ T.Con @Rn defaultPos $ mkVar defaultPos "Bool",
      ErrLine,
      Error "A suitable ‘Bool’ type must have exactly two nullary constructors named ‘True’ and ‘False’."
    ]
{-# NOINLINE expectedBool #-}

-- It is unlikely that this error can be triggered. But I feel that it is
-- better to have an error message at hand should it be needed than crashing
-- the compiler.
noNormalform :: TcType -> PosError
noNormalform t = PosError (pos t) [Error "Malformed type:", Error t]
{-# NOINLINE noNormalform #-}

missingUse :: ProgVar -> Var -> PosError
missingUse var Var {varLocation = loc} =
  PosError
    loc
    [ Error "Linear variable",
      Error var,
      Error "is unused."
    ]
{-# NOINLINE missingUse #-}

invalidConsumed :: Pos -> ProgVar -> Var -> Pos -> PosError
invalidConsumed contextLoc name var loc =
  PosError
    loc
    [ Error "Linear variable",
      Error name,
      ErrLine,
      Error "   bound at",
      Error (varLocation var),
      ErrLine,
      Error "Consumed in unrestricted context",
      ErrLine,
      Error "   started at",
      Error contextLoc
    ]
{-# NOINLINE invalidConsumed #-}

linVarUsedTwice :: Pos -> Pos -> ProgVar -> Var -> PosError
linVarUsedTwice loc1 loc2 name var =
  PosError
    (max loc1 loc2)
    [ Error "Linear variable",
      Error name,
      Error "is used twice.",
      ErrLine,
      Error "Bound at:",
      Error (varLocation var),
      ErrLine,
      Error " Used at:",
      Error (min loc1 loc2),
      ErrLine,
      Error "         ",
      Error (max loc1 loc2)
    ]
{-# NOINLINE linVarUsedTwice #-}

noArrowType :: RnExp -> TcType -> PosError
noArrowType e t =
  PosError
    (pos e)
    [ Error "Type of",
      ErrLine,
      Error "  ",
      Error e,
      ErrLine,
      Error "is neither a function type nor convertible to a function type:",
      ErrLine,
      Error "  ",
      Error t
    ]
{-# NOINLINE noArrowType #-}

noForallType :: RnExp -> TcType -> PosError
noForallType e t =
  PosError
    (pos e)
    [ Error "Type of",
      ErrLine,
      Error "  ",
      Error e,
      ErrLine,
      Error "is neither a forall type nor convertible to a forall type:",
      ErrLine,
      Error "  ",
      Error t
    ]
{-# NOINLINE noForallType #-}

typeConstructorNParams :: Pos -> NonEmpty RnType -> Int -> Int -> PosError
typeConstructorNParams loc ts !given !expected =
  PosError
    loc
    [ Error "Invalid type application",
      ErrLine,
      Error "  ",
      Error $ foldl1 (T.App loc) ts,
      ErrLine,
      Error "Type constructor",
      Error $ NE.head ts,
      Error "needs",
      Error expected,
      Error $ plural expected "parameter," "paramters,",
      Error given,
      Error "provided."
    ]
{-# NOINLINE typeConstructorNParams #-}

cyclicAliases :: [(Pos, TypeVar, TypeAlias Rn)] -> PosError
cyclicAliases aliases =
  PosError errLoc $
    Error "Cycle in type synonym declarations." :
    concat
      [ concat
          [ [ ErrLine,
              Error $ "  " ++ showLoc loc
            ],
            aliasHead name (aliasParams a),
            [ Error "=",
              Error (aliasType a)
            ]
          ]
        | (loc, name, a) <- aliases
      ]
  where
    errLoc = minimum positions
    locSize = maximum (length . show <$> positions)
    positions = fmap (\(p, _, _) -> p) aliases
    showLoc (show -> l) = l ++ ":" ++ replicate (locSize - length l) ' '
    aliasHead name params = Error "type" : Error name : [Error p | (p, _) <- params]
{-# NOINLINE cyclicAliases #-}

invalidNominalKind :: Pos -> String -> TypeVar -> K.Kind -> NonEmpty K.Kind -> PosError
invalidNominalKind loc nomKind name actual allowed =
  PosError
    loc
    [ Error "The declared type of",
      Error name,
      Error "is",
      Error actual,
      ErrLine,
      Error $ "‘" ++ nomKind ++ "’",
      Error "declarations can only declare types with",
      Error $ plural allowed "kind" "kinds",
      Error $ joinOr $ fmap show allowed,
      Error "(the default)."
    ]
{-# NOINLINE invalidNominalKind #-}

mismatchedBind :: PTVar -> TcType -> PosError
mismatchedBind var t =
  PosError (pos var) $
    Error (choose "Binding of variable" "Binding of type variable") :
    Error var :
    Error "does not align with type" :
    ErrLine :
    showType t Nothing
  where
    choose x y = either (const x) (const y) var
{-# NOINLINE mismatchedBind #-}

invalidPatternExpr :: String -> Pos -> TcType -> TcType -> PosError
invalidPatternExpr desc loc scrutTy tyNF =
  PosError loc $
    errUnline
      [ [Error desc, Error "has type"],
        showType scrutTy (Just tyNF),
        [Error "which is not allowed in pattern expressions."]
      ]
{-# NOINLINE invalidPatternExpr #-}

invalidSessionCaseBranch :: E.CaseBranch f Rn -> PosError
invalidSessionCaseBranch branch = PosError (E.branchPos branch) [Error msg]
  where
    msg = "Branches of a receiving case must bind exactly one variable."
{-# NOINLINE invalidSessionCaseBranch #-}

mismatchedCaseConstructor :: Pos -> TcType -> ProgVar -> PosError
mismatchedCaseConstructor loc ty con =
  PosError
    loc
    [ Error con,
      Error "is not a constructor for type",
      Error ty
    ]
{-# NOINLINE mismatchedCaseConstructor #-}

missingCaseBranches :: Pos -> [ProgVar] -> PosError
missingCaseBranches loc branches =
  PosError loc $
    Error "Incomplete case. Missing" :
    Error (plural branches "branch:" "branches:") :
    missingBranches branches
{-# NOINLINE missingCaseBranches #-}

noSingularConstructorType :: Pos -> TcType -> [ProgVar] -> PosError
noSingularConstructorType loc ty branches =
  PosError loc $
    Error "Values of type" :
    ErrLine :
    Error "  " :
    Error ty :
    Error "cannot appear as the right hand side of a let-pattern." :
    ErrLine :
    Error "Too many constructors. Unhandled " :
    Error (plural branches "constructor:" "constructors:") :
    missingBranches branches
{-# NOINLINE noSingularConstructorType #-}

missingBranches :: [ProgVar] -> [ErrorMessage]
missingBranches branches =
  concat
    [ [ErrLine, Error "  ", branch]
      | branch <- truncate 3 (Error "...") (Error <$> branches)
    ]

emptyCaseExpr :: Pos -> PosError
emptyCaseExpr loc = PosError loc [Error "Empty case expression."]
{-# NOINLINE emptyCaseExpr #-}

class Position a => BranchSpec a where
  displayBranchError :: a -> [ErrorMessage]

instance BranchSpec ProgVar where
  displayBranchError p = [Error "branch", Error p]
  {-# INLINE displayBranchError #-}

newtype WildcardBranch = WildcardBranch Pos

instance Position WildcardBranch where
  pos (WildcardBranch p) = p
  {-# INLINE pos #-}

instance BranchSpec WildcardBranch where
  displayBranchError _ = [Error "wildcard branch"]
  {-# INLINE displayBranchError #-}

data CondBranch = CondThen Pos | CondElse Pos

instance Position CondBranch where
  pos = \case
    CondThen p -> p
    CondElse p -> p
  {-# INLINE pos #-}

instance BranchSpec CondBranch where
  displayBranchError = \case
    CondThen _ -> [Error "‘then’ branch"]
    CondElse _ -> [Error "‘else’ branch"]
  {-# INLINE displayBranchError #-}

branchedConsumeDifference ::
  (BranchSpec a, BranchSpec b) => ProgVar -> Var -> a -> Pos -> b -> PosError
branchedConsumeDifference name var consumeBranch consumeLoc otherBranch =
  PosError consumeLoc $
    concat
      [ [ Error "Linear variable",
          ErrLine,
          Error "  ",
          Error name,
          Error ":",
          Error (varType var),
          ErrLine,
          Error "is not consumed in"
        ],
        displayBranchError otherBranch,
        [ Error "at",
          Error (pos otherBranch),
          ErrLine,
          Error "but is consumed in"
        ],
        displayBranchError consumeBranch,
        [ Error "at",
          Error (pos consumeBranch)
        ]
      ]
{-# NOINLINE branchedConsumeDifference #-}

branchPatternBindingCount :: Pos -> ProgVar -> Int -> Int -> PosError
branchPatternBindingCount loc name !expected !given =
  PosError
    loc
    [ Error "The constructor",
      Error name,
      Error "should have",
      Error (pluralZ expected "no arguments," "one argument," (show expected ++ " arguments,")),
      Error "but has been given",
      Error (pluralZ given "none" "one" (show given))
    ]
{-# NOINLINE branchPatternBindingCount #-}

unnecessaryWildcard :: Pos -> PosError
unnecessaryWildcard loc = PosError loc [Error msg]
  where
    msg = "Unnecessary wildcard. All possible branches are handled."
{-# NOINLINE unnecessaryWildcard #-}

wildcardNotAllowed :: Pos -> Pos -> PosError
wildcardNotAllowed wildLoc caseLoc =
  PosError
    wildLoc
    [ Error "Wildcards are not allowed in the context started at",
      Error caseLoc
    ]
{-# NOINLINE wildcardNotAllowed #-}

protocolConAsValue :: Pos -> ProgVar -> TypeVar -> PosError
protocolConAsValue loc con parent =
  PosError
    loc
    [ Error "Constructor",
      Error con,
      Error "is a protocol constructor for type",
      Error parent,
      ErrLine,
      Error "Protocol constructors can only be used in case patterns and arguments to ‘select’."
    ]
{-# NOINLINE protocolConAsValue #-}

builtinMissingApp :: RnExp -> String -> PosError
builtinMissingApp e expected =
  PosError
    (pos e)
    [ Error "Operator",
      Error e,
      Error "must be followed by a",
      Error expected
    ]
{-# NOINLINE builtinMissingApp #-}

showType :: TcType -> Maybe TcType -> [ErrorMessage]
showType t mNF
  | Just tNF <- mNF,
    Eq.Alpha t /= Eq.Alpha tNF =
    [ Error $ MsgTag " [NF]",
      Error tNF,
      ErrLine,
      Error $ MsgTag "[LIT]",
      Error t
    ]
  | otherwise =
    [indent, Error t]

errUnline :: [[ErrorMessage]] -> [ErrorMessage]
errUnline = List.intercalate [ErrLine]

indent :: ErrorMessage
indent = Error "   "
