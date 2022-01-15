{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}

module AlgST.Util.ErrorMessage
  ( ErrorMessage (..),
    ErrorMsg (..),
    PosError (..),
    MsgTag (..),
    redFGStyling,
  )
where

import AlgST.Parse.Unparser
import AlgST.Syntax.Expression as E
import qualified AlgST.Syntax.Kind as K
import qualified AlgST.Syntax.Type as T
import Data.Coerce
import Data.List (intercalate)
import Syntax.Base
import Syntax.ProgramVariable
import Syntax.TypeVariable
import System.Console.ANSI

-- | Error class and instances
class ErrorMsg a where
  msg :: a -> String

  -- | The 'SGR' the output of 'msg' should use. An empty list corresponds to
  -- no special rendering.
  msgStyling :: a -> [SGR]

redFGStyling :: [SGR]
redFGStyling = [SetColor Foreground Vivid Red]

-- | Specifies that this part of the error message is not as important as the
-- surroundings. When rendered with colors this uses a subdued highlighting.
newtype MsgTag a = MsgTag a

data ErrorMessage where
  Error :: ErrorMsg a => a -> ErrorMessage
  ErrLine :: ErrorMessage

data PosError = PosError !Pos [ErrorMessage]

instance Position PosError where
  pos (PosError p _) = p

instance Unparse (T.XType x) => ErrorMsg (T.Type x) where
  msg = show
  msgStyling _ = redFGStyling

instance ErrorMsg String where
  msg = id
  msgStyling _ = []

instance (Unparse (E.XExp x), Unparse (T.XType x)) => ErrorMsg (E.Exp x) where
  msg = show
  msgStyling _ = redFGStyling

instance ErrorMsg ProgVar where
  msg = show
  msgStyling _ = redFGStyling

instance ErrorMsg TypeVar where
  msg = show
  msgStyling _ = redFGStyling

instance (ErrorMsg a, ErrorMsg b) => ErrorMsg (Either a b) where
  msg = either msg msg
  msgStyling = either msgStyling msgStyling

instance ErrorMsg Pos where
  msg = show
  msgStyling _ = []

instance ErrorMsg K.Kind where
  msg = show
  msgStyling _ = redFGStyling

instance ErrorMsg Int where
  msg = show
  msgStyling _ = redFGStyling

instance ErrorMsg a => ErrorMsg (MsgTag a) where
  msg = coerce (msg @a)
  msgStyling (MsgTag a) = msgStyling a ++ [SetConsoleIntensity NormalIntensity]

instance Unparse (T.XType x) => ErrorMsg [T.Type x] where
  msg = showTypeList
  msgStyling _ = redFGStyling

showTypeList :: Unparse (T.XType x) => [T.Type x] -> String
showTypeList ts = "[" ++ intercalate ", " types ++ "]"
  where
    types = map show ts
