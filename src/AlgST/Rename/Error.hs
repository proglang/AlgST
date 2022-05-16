{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}

module AlgST.Rename.Error where

import AlgST.Syntax.Name
import AlgST.Util
import AlgST.Util.ErrorMessage
import Control.Monad.Validate
import Data.DList.DNonEmpty (DNonEmpty)
import Data.DList.DNonEmpty qualified as DNE
import Data.List qualified as List
import Syntax.Base

type Errors = DNonEmpty Diagnostic

type MonadErrors = MonadValidate Errors

addError :: MonadErrors m => Diagnostic -> m ()
addError !e = dispute (DNE.singleton e)

fatalError :: MonadErrors m => Diagnostic -> m a
fatalError !e = refute (DNE.singleton e)

data AmbiguousOrigin
  = AmbiguousImport !Pos !ModuleName
  | AmbiguousDefine !Pos

instance Position AmbiguousOrigin where
  pos = \case
    AmbiguousImport p _ -> p
    AmbiguousDefine p -> p

ambiguousUsage :: Pos -> NameW scope -> [AmbiguousOrigin] -> Diagnostic
ambiguousUsage loc name amb =
  PosError loc $ List.intercalate [ErrLine] $ intro : fmap choice (sortPos amb)
  where
    intro =
      [ Error "Usage of identifier",
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
