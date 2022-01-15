module BuiltinsSpec where

import AlgST.Builtins
import AlgST.Rename
import AlgST.Syntax.Program
import AlgST.Typing
import Data.Foldable
import qualified Data.Map.Strict as Map
import Test.Golden
import Test.Hspec

spec :: Spec
spec = do
  it "kind checks" do
    let res = runRename builtins $ renameProgram builtins >>= checkProgram
    case res of
      Left errs -> expectationFailure (plainErrors errs)
      Right _ -> pure ()

  context "predefined names" do
    for_ types \name ->
      specify (show name) do Map.member name (programTypes builtins)
    for_ values \name ->
      specify (show name) do Map.member name (programValues builtins)
    for_ imports \name ->
      specify (show name) do Map.member name (programImports builtins)
