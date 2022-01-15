{-# LANGUAGE LambdaCase #-}

-- | This module provides tools to prettify & format errors with ANSI colors
-- for terminals.
module AlgST.Util.Error
  ( PosError,
    OutputMode (..),
    renderErrors,
    renderErrors',
    formatErrorMessages,
    internalError,
  )
where

import AlgST.Util
import AlgST.Util.ErrorMessage
import AlgST.Util.Output
import Data.CallStack
import Data.Foldable
import Data.Function
import qualified Data.List as List
import Data.Maybe
import Data.Monoid (Endo (..))
import Syntax.Base
import Prelude hiding (truncate)

-- | Renders a single error as 'Plain'. Multiple errors are rendered
-- interspersed with newlines and not truncated.
instance Show PosError where
  showsPrec _ e = showList [e]
  showList = renderErrors' Nothing Plain ""

-- | Renders a list of errors for the given 'OutputMode'. The errors are
-- ordered by location and then truncated to at most ten.
renderErrors :: OutputMode -> String -> [PosError] -> String
renderErrors m fileName errs = renderErrors' (Just 10) m fileName errs ""

-- | Like 'renderErrors' but truncates based on the first parameter.
renderErrors' :: Maybe Int -> OutputMode -> String -> [PosError] -> ShowS
renderErrors' maxErrs mode fileName errs =
  sortPos errs
    & fmap (Endo . render)
    & maybe id (\n -> truncate n truncMsg) maxErrs
    & List.intersperse (Endo $ showChar '\n')
    & fold
    & appEndo
  where
    render = formatErrorMessagesS mode fileName
    truncMsg = Endo $ showString "\nToo many errors. Truncated."

-- | Formats a single error.
formatErrorMessages :: OutputMode -> String -> PosError -> String
formatErrorMessages mode fname err = formatErrorMessagesS mode fname err ""

formatErrorMessagesS :: OutputMode -> String -> PosError -> ShowS
formatErrorMessagesS mode fname (PosError p es)
  | null es = id
  | otherwise = header . appEndo body
  where
    header = styleHeader mode fname p
    body = foldMap (Endo . styledMessage mode) es

styledMessage :: OutputMode -> ErrorMessage -> ShowS
styledMessage mode = \case
  -- Every part has to be bolded by itself instead of the whole message because
  -- resetting the color after a colored part in the error message would reset
  -- the boldness for the rest of the message as well.
  Error e -> showChar ' ' . applyStyle mode (style (boldSGR : msgStyling e)) (msg e ++)
  ErrLine -> showString "\n\t"

styleHeader :: OutputMode -> String -> Pos -> ShowS
styleHeader mode f p = applyStyle mode styleBold $ start . location . endSpace . end
  where
    start
      | null f = showChar '\n'
      | otherwise = showChar '\n' . showString f . showChar ':'
    location
      | p == defaultPos = id
      | otherwise = shows p . showChar ':'
    endSpace
      | null f && p == defaultPos = id
      | otherwise = showChar ' '
    end = applyStyle mode styleRed $ showString "error:\n\t"

-- | Internal errors
internalError :: (HasCallStack, Show a, Position a) => String -> a -> b
internalError fun syntax =
  error $
    show (pos syntax)
      ++ ": Internal error at "
      ++ fun
      ++ ": "
      ++ show syntax
