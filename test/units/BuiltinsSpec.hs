module BuiltinsSpec where

import AlgST.Builtins
import AlgST.Builtins.Names
import AlgST.Rename
import AlgST.Rename.Fresh
import AlgST.Typing
import Test.Golden
import Test.Hspec

spec :: Spec
spec = do
  it "kind checks" do
    let res = runRename (renameModule builtins) >>= checkModule
    case runFresh BuiltinsModule res of
      Left errs -> expectationFailure (plainErrors errs)
      Right _ -> pure ()

--  TODO: Reenable these tests.
--
--  context "predefined names" do
--    for_ types \name ->
--      specify (show name) do Map.member name (moduleTypes builtins)
--    for_ values \name ->
--      specify (show name) do Map.member name (moduleValues builtins)
--    for_ imports \name ->
--      specify (show name) do Map.member name (moduleImports builtins)
