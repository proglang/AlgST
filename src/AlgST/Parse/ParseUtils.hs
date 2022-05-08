{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}

module AlgST.Parse.ParseUtils
  ( -- * Parse monad
    ParseM,
    runParseM,
    UnscopedName (..),
    scopeName,

    -- * Errors
    addError,
    addErrors,
    fatalError,

    -- ** Error messages
    errorNoTermLinLambda,
    errorRecNoTermLambda,
    errorMultipleWildcards,
    errorMisplacedPairCon,
    errorDuplicateBind,

    -- * Operators
    resolveOpSeq,

    -- * Type declarations
    typeConstructors,

    -- * Assembling of modules
    ModuleBuilder,
    runModuleBuilder,
    moduleValueDecl,
    moduleValueBinding,
    moduleTypeDecl,
    addImport,

    -- * Checking for duplicates
    DuplicateError,
    insertNoDuplicates,
    mergeNoDuplicates,
  )
where

import AlgST.Parse.Operators
import AlgST.Parse.Phase
import AlgST.Syntax.Decl
import AlgST.Syntax.Expression qualified as E
import AlgST.Syntax.Module
import AlgST.Syntax.Name
import AlgST.Util.ErrorMessage
import Control.Arrow
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Validate
import Data.DList.DNonEmpty (DNonEmpty)
import Data.DList.DNonEmpty qualified as DL
import Data.Function
import Data.Functor.Identity
import Data.List.NonEmpty (NonEmpty (..))
import Data.Map.Merge.Strict qualified as Merge
import Data.Map.Strict qualified as Map
import Data.Maybe
import Data.Singletons
import Syntax.Base

type ParseM = Validate (DNonEmpty Diagnostic)

-- | Evaluates a value in the 'ParseM' monad producing a list of errors and
-- maybe a result.
runParseM :: ParseM a -> Either (NonEmpty Diagnostic) a
runParseM = mapErrors DL.toNonEmpty >>> runValidate

newtype UnscopedName = UName (forall scope. PName scope)

scopeName :: UnscopedName -> PName scope
scopeName (UName n) = n

addError :: Pos -> [ErrorMessage] -> ParseM ()
addError !p err = addErrors [PosError p err]

addErrors :: [Diagnostic] -> ParseM ()
addErrors [] = pure ()
addErrors (e : es) = dispute $ DL.fromNonEmpty $ e :| es

fatalError :: Diagnostic -> ParseM a
fatalError = refute . DL.singleton

resolveOpSeq :: Parenthesized -> OpSeq first (Located (ProgVar PStage), [PType]) -> ParseM PExp
resolveOpSeq ps = mapErrors DL.fromList . parseOperators ps

typeConstructors ::
  TypeVar PStage ->
  TypeDecl Parse ->
  NameMap Values (ConstructorDecl Parse)
typeConstructors = declConstructors originAt originAt

type IncompleteValueDecl = Maybe (Located (PName Values), PType)

type ModuleBuilder =
  Kleisli (StateT IncompleteValueDecl ParseM) PModule PModule

runModuleBuilder :: PModule -> ModuleBuilder -> ParseM PModule
runModuleBuilder base builder =
  evalStateT (runKleisli (builder >>> completePrevious) base) Nothing

completePrevious :: ModuleBuilder
completePrevious = Kleisli \p -> do
  msig <- get
  case msig of
    Nothing ->
      pure p
    Just (loc :@ name, sig) -> do
      put Nothing
      let decl = SignatureDecl (OriginUser loc) sig
      imports <- lift $ insertNoDuplicates name decl (moduleSigs p)
      pure p {moduleSigs = imports}

moduleValueDecl :: Located (ProgVar PStage) -> PType -> ModuleBuilder
moduleValueDecl valueName ty =
  completePrevious >>> Kleisli \p -> do
    put $ Just (valueName, ty)
    pure p

moduleValueBinding :: Located (ProgVar PStage) -> [Located AName] -> PExp -> ModuleBuilder
moduleValueBinding valueName params e = Kleisli \p0 -> do
  mincomplete <- get
  p <-
    -- If there is an incomplete definition which does not match the current
    -- variable, we have to add it to the "imported" signatures.
    if
        | Just (prevName, _) <- mincomplete,
          onUnL (/=) valueName prevName ->
          runKleisli completePrevious p0
        | otherwise ->
          pure p0

  -- Re-read the incomplete binding, might be changed by the call to
  -- 'validateNotIncomplete' and remember that there is no incomplete binding
  -- now.
  mincomplete' <- get <* put Nothing
  case mincomplete' of
    Nothing -> lift do
      addError
        (pos valueName)
        [ Error "Binding of",
          Error valueName,
          Error "should be preceeded by its declaration."
        ]
      pure p
    Just (defLoc :@ _, ty) -> lift do
      let decl =
            ValueDecl
              { valueOrigin = OriginUser defLoc,
                valueType = ty,
                valueParams = params,
                valueBody = e
              }
      parsedValues' <-
        insertNoDuplicates
          (unL valueName)
          (Right decl)
          (moduleValues p)
      when (unL valueName `Map.member` moduleSigs p) do
        addErrors [uncurryL errorImportShadowed valueName]
      pure p {moduleValues = parsedValues'}

moduleTypeDecl :: TypeVar PStage -> TypeDecl Parse -> ModuleBuilder
moduleTypeDecl v tydecl =
  completePrevious >>> Kleisli \p -> do
    parsedTypes' <- lift $ insertNoDuplicates v tydecl (moduleTypes p)
    let constructors = Left <$> typeConstructors v tydecl
    parsedValues' <- lift $ mergeNoDuplicates (moduleValues p) constructors
    pure p {moduleTypes = parsedTypes', moduleValues = parsedValues'}

addImport :: Located Import -> ModuleBuilder
addImport i = Kleisli \m -> pure $ m {moduleImports = i : moduleImports m}

-- | Inserts the value under the given key into the map. If there is already a
-- value under that key an error as with 'errorMultipleDeclarations' is added
-- and the value is not changed.
insertNoDuplicates ::
  (DuplicateError k v, Ord k) => k -> v -> Map.Map k v -> ParseM (Map.Map k v)
insertNoDuplicates k v m = mergeNoDuplicates m $ Map.singleton k v

-- | Merges two maps, for any overlapping keys an error as with
-- 'errorMultipleDeclarations' is added.
--
-- In case of any merge duplicates the unmerged map will be returned.
mergeNoDuplicates ::
  (DuplicateError k v, Ord k) => Map.Map k v -> Map.Map k v -> ParseM (Map.Map k v)
mergeNoDuplicates m new =
  merge m new
    & tolerate
    & fmap (fromMaybe m)
  where
    merge =
      Merge.mergeA
        Merge.preserveMissing
        Merge.preserveMissing
        (Merge.zipWithAMatched dupError)
    dupError k v1 v2 =
      fatalError $ duplicateError k v1 v2

class DuplicateError k a where
  duplicateError :: k -> a -> a -> Diagnostic

-- | Message for duplicate type declarations.
instance DuplicateError (Name PStage Types) (TypeDecl Parse) where
  duplicateError = errorMultipleDeclarations

-- | Message for a duplicated top-level value declaration. This includes both
-- constrcutor names between two declarations, and top-level functions.
instance
  DuplicateError
    (Name PStage Values)
    (Either (ConstructorDecl Parse) (ValueDecl Parse))
  where
  duplicateError = errorMultipleDeclarations

instance DuplicateError (Name PStage Values) (SignatureDecl Parse) where
  duplicateError = errorMultipleDeclarations

-- | Message for a duplicated constructor inside a type declaration.
instance DuplicateError (Name PStage Values) (Pos, [PType]) where
  duplicateError v (p1, _) (p2, _) = errorMultipleDeclarations v p1 p2

-- | Message for a duplicate branch in a case expression:
--
-- > case … of { A -> …, A -> … }
instance DuplicateError (Name PStage Values) (E.CaseBranch f Parse) where
  duplicateError = errorDuplicateBranch

-- | Messages for any form of duplicate binding:
--
-- * patterns
-- * lambda abstractions (not yet implemented)
-- * type parameters
-- * top-level function parameters
instance ErrorMsg a => DuplicateError a Pos where
  duplicateError = errorDuplicateBind

errorMultipleDeclarations ::
  (ErrorMsg a, Position p1, Position p2) => a -> p1 -> p2 -> Diagnostic
errorMultipleDeclarations a (pos -> p1) (pos -> p2) =
  PosError
    (max p1 p2)
    [ Error "Multiple declarations of",
      Error a,
      ErrLine,
      Error "Declared at:",
      Error (min p1 p2),
      ErrLine,
      Error "            ",
      Error (max p1 p2)
    ]

errorDuplicateBind :: ErrorMsg v => v -> Pos -> Pos -> Diagnostic
errorDuplicateBind name p1 p2 =
  PosError
    (min p1 p2)
    [ Error "Conflicting bindings for",
      Error name,
      ErrLine,
      Error "Bound at:",
      Error (min p1 p2),
      ErrLine,
      Error "         ",
      Error (max p1 p2)
    ]
{-# NOINLINE errorDuplicateBind #-}

errorDuplicateBranch :: ProgVar PStage -> E.CaseBranch f x -> E.CaseBranch f x -> Diagnostic
errorDuplicateBranch name (pos -> p1) (pos -> p2) =
  PosError
    (max p1 p2)
    [ Error "Duplicate case alternative",
      Error name,
      ErrLine,
      Error "Branches at:",
      Error (min p1 p2),
      ErrLine,
      Error "            ",
      Error (max p1 p2)
    ]

errorImportShadowed :: Pos -> ProgVar PStage -> Diagnostic
errorImportShadowed loc name =
  PosError
    loc
    [ Error "Declaration of",
      Error name,
      Error "shadows an import/builtin of the same name."
    ]
{-# NOINLINE errorImportShadowed #-}

-- | An error message for when a lambda binds only type variables but uses the
-- linear arrow @-o@. This combination does not make sense, therefore we do not
-- allow it.
errorNoTermLinLambda :: Pos -> Pos -> Diagnostic
errorNoTermLinLambda lambdaLoc arrowLoc =
  PosError
    arrowLoc
    [ Error "Lambda at",
      Error lambdaLoc,
      Error "binds only type variables.",
      ErrLine,
      Error "Use the unrestricted arrow ‘->’ for this case."
    ]
{-# NOINLINE errorNoTermLinLambda #-}

errorRecNoTermLambda :: Pos -> Diagnostic
errorRecNoTermLambda p = PosError p [Error msg1, ErrLine, Error msg2]
  where
    msg1 =
      "• a ‘rec’ expression's right-hand side must consist of a \
      \lambda abstraction."
    msg2 =
      "• a ‘rec’ expression must bind at least one non-type parameter in \
      \their right-hand side lambda abstraction."
{-# NOINLINE errorRecNoTermLambda #-}

errorMultipleWildcards ::
  E.CaseBranch Identity Parse -> E.CaseBranch Identity Parse -> Diagnostic
errorMultipleWildcards x y =
  PosError
    (pos b2)
    [ Error "Multiple wildcards in case expression:",
      Error $ runIdentity $ E.branchBinds b1,
      Error $ runIdentity $ E.branchBinds b2,
      ErrLine,
      Error "Branches at:",
      Error (pos b1),
      ErrLine,
      Error "            ",
      Error (pos b2)
    ]
  where
    (b1, b2) =
      if pos x < pos y
        then (x, y)
        else (y, x)

errorMisplacedPairCon ::
  forall (s :: Scope) proxy. SingI s => Pos -> proxy s -> Diagnostic
errorMisplacedPairCon loc _ =
  PosError
    loc
    [ Error "Pair constructor",
      Error $ PairCon @s,
      Error "cannot be used as",
      Error . id @String $
        eitherName @s
          "a type constructor."
          "an expression.",
      ErrLine,
      Error "It can only appear in patterns and with ‘select’."
    ]
{-# NOINLINE errorMisplacedPairCon #-}
