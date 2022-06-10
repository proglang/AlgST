{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module AlgST.Rename.Error where

import AlgST.Syntax.Name
import AlgST.Util
import AlgST.Util.ErrorMessage
import Control.Monad.Validate
import Data.DList.DNonEmpty qualified as DNE
import Data.List qualified as List
import Data.Singletons
import Language.Haskell.TH.Syntax (Lift)
import Syntax.Base

type MonadErrors = MonadValidate DErrors

addError :: MonadErrors m => Diagnostic -> m ()
addError !e = dispute (DNE.singleton e)

fatalError :: MonadErrors m => Diagnostic -> m a
fatalError !e = refute (DNE.singleton e)

data AmbiguousOrigin
  = AmbiguousImport !Pos !ModuleName
  | AmbiguousDefine !Pos
  deriving stock (Lift)

instance Position AmbiguousOrigin where
  pos = \case
    AmbiguousImport p _ -> p
    AmbiguousDefine p -> p

data NameKind = Con | Var

nameKind :: forall (scope :: Scope) proxy. SingI scope => NameKind -> proxy scope -> String
nameKind k _ =
  eitherName @scope
    (case k of Con -> "type"; Var -> "type variable")
    (case k of Con -> "constructor"; Var -> "variable")

ambiguousUsage ::
  forall scope.
  SingI scope =>
  Pos ->
  NameKind ->
  NameW scope ->
  [AmbiguousOrigin] ->
  Diagnostic
ambiguousUsage loc k name amb =
  PosError loc $ List.intercalate [ErrLine] $ intro : fmap choice (sortPos amb)
  where
    intro =
      [ Error "Usage of",
        Error $ nameKind k name,
        Error name,
        Error "is ambiguous. It may refer to"
      ]
    choice a =
      [ Error "  •",
        Error (description a),
        ErrLine,
        Error "   ",
        Error (location a)
      ]
    description = \case
      AmbiguousImport {} -> "the import from"
      AmbiguousDefine {} -> "the local definition"
    location amb =
      MsgTag $ "at " ++ show (pos amb)
{-# NOINLINE ambiguousUsage #-}

unknownImportItem :: Pos -> ModuleName -> Scope -> Located Unqualified -> Diagnostic
unknownImportItem stmtLoc modName scope (itemLoc :@ item) =
  PosError itemLoc $
    scopePrefix
      [ Error item,
        Error "is not exported by module",
        Error modName,
        ErrLine,
        Error "In import statement at",
        Error stmtLoc
      ]
  where
    scopePrefix = case scope of
      Types -> (Error "Type" :)
      Values -> id
{-# NOINLINE unknownImportItem #-}

unboundName ::
  forall stage scope. SingI scope => Pos -> NameKind -> Name stage scope -> Diagnostic
unboundName loc kind v =
  PosError loc [Error "Unbound", Error $ nameKind kind v, Error v]
{-# NOINLINE unboundName #-}
