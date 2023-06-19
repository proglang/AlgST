{-# LANGUAGE FlexibleContexts, LambdaCase #-}
{-# LANGUAGE BlockArguments #-}
{- |
Module      :  Parse.ParseUtils
Description :  <optional short text displayed on contents page>
Copyright   :  (c) <Authors or Affiliations>
License     :  <license>

Maintainer  :  <email>
Stability   :  unstable | experimental | provisional | stable | frozen
Portability :  portable | non-portable (<reason>)

<module description starting at first column>
-}

module Parse.ParseUtils where

import           Syntax.Base
import           Syntax.Program
import qualified Syntax.Expression as E
import qualified Syntax.Kind as K
import           Syntax.MkName (mkTrue, mkFalse, mkTupleLabels)
import qualified Validation.Subkind as SK
import           Validation.Kinding (synthetise)
import qualified Syntax.Type as T
import           Util.Error
import           Util.FreestState

import           Control.Monad.State
import           Data.List       ( find )
import qualified Data.Map.Strict as Map
import           Data.Bitraversable (bimapM)

type FreestStateT = StateT FreestS (Either ErrorType)

-- Modules

mkSpan :: Located a => a -> FreestStateT Span
mkSpan a = do
  let (Span p1 p2 _) = getSpan a
  f <- getFileName
  maybe (Span p1 p2 f) (Span p1 p2) <$> getModuleName

mkSpanSpan :: (Located a, Located b) => a -> b -> FreestStateT Span
mkSpanSpan a b = do
  let (Span p1 _ _) = getSpan a
  let (Span _ p2 _) = getSpan b
  f <- getFileName
  maybe (Span p1 p2 f) (Span p1 p2) <$> getModuleName

mkSpanFromSpan :: Located a => Span -> a -> FreestStateT Span
mkSpanFromSpan (Span p1 _ _) a = do
  let (Span _ p2 _) = getSpan a
  f <- getFileName
  maybe (Span p1 p2 f) (Span p1 p2) <$> getModuleName

liftModToSpan :: Span -> FreestStateT Span
liftModToSpan (Span p1 p2 _) = do
  f <- getFileName
  maybe (Span p1 p2 f) (Span p1 p2) <$> getModuleName

-- Parse errors

-- checkDupField :: Variable -> T.TypeMap -> FreestState ()
checkDupField :: MonadState FreestS m => Variable -> Map.Map Variable v -> m ()
checkDupField x m =
  when (x `Map.member` m) $ addError $ MultipleFieldDecl (getSpan x) (getSpan k) x
  where
    (k,_) = Map.elemAt (Map.findIndex x m) m

checkDupCase :: Variable -> E.FieldMap -> FreestStateT ()
checkDupCase x m =
  when (x `Map.member` m) $ addError $ RedundantPMatch (getSpan x) x

checkDupBind :: Variable -> [Variable] -> FreestStateT ()
checkDupBind x xs
  | isWild x = return ()
  | otherwise = case find (== x) xs of
    Just y  -> addError $ DuplicateVar (getSpan y) "program" x (getSpan x)
    Nothing -> return ()

-- checkDupKindBind :: Bind K.Kind a -> [Bind K.Kind a] -> FreestStateT ()
-- checkDupKindBind (Bind p x _ _) bs =
--   case find (\(Bind _ y _ _) -> y == x) bs of
--     Just (Bind p' _ _ _) -> addError $ DuplicateTVar p' x p
--     Nothing                -> return ()

checkDupCons :: (Variable, [T.Type]) -> [(Variable, [T.Type])] -> FreestStateT ()
checkDupCons (x, _) xts
  | any compare xts = addError $ DuplicateFieldInDatatype (getSpan x) x pos
  | otherwise =
      gets (flip (Map.!?) x . varEnv) >>= \case
       Just _  -> addError $ MultipleDeclarations (getSpan x) x pos
       Nothing -> return ()
  where
    compare (y, _) = y == x
    pos = maybe defaultSpan (getSpan . fst) (find compare xts)

checkDupProgVarDecl :: Variable -> FreestStateT ()
checkDupProgVarDecl x = do
  vEnv <- gets varEnv
  case vEnv Map.!? x of
    Just _  -> addError $ MultipleDeclarations (getSpan x) x (pos vEnv)
    Nothing -> return ()
 where
    pos vEnv = getSpan $ fst $ Map.elemAt (Map.findIndex x vEnv) vEnv

checkDupTypeDecl :: Variable -> FreestStateT ()
checkDupTypeDecl a = do
  tEnv <- gets typeEnv
  case tEnv Map.!? a of
    Just _   -> addError $ MultipleTypeDecl (getSpan a) a (pos tEnv)-- (getSpan s)
    Nothing  -> return ()
 where
    pos tEnv = getSpan $ fst $ Map.elemAt (Map.findIndex a tEnv) tEnv

-- verifies if there is any duplicated var in any patern, or nested pattern
checkDupVarPats :: [E.Pattern] -> FreestStateT ()
checkDupVarPats ps = void $ checkDupVarPats' ps []

checkDupVarPats' :: [E.Pattern] -> [Variable] -> FreestStateT [Variable]
checkDupVarPats' [] vs = return vs
checkDupVarPats' ((E.PatCons _ cs):xs) vs = checkDupVarPats' cs vs >>= checkDupVarPats' xs
checkDupVarPats' ((E.PatVar  v)   :xs) vs = do
   case find clause vs of
    Nothing -> checkDupVarPats' xs (v:vs)
    Just v2 -> addError (DuplicateVar (getSpan v) "program" v2 (getSpan v2))
            >> checkDupVarPats' xs (v:vs)
  where clause v2 = not (isWild v) && v == v2

-- OPERATORS

binOp :: E.Exp -> Variable -> E.Exp -> E.Exp
binOp l op r = E.App s (E.App (getSpan l) (E.Var (getSpan op) op) l) r
  where s = Span (startPos $ getSpan l) (endPos $ getSpan r) (defModule $ getSpan l)

unOp :: Variable -> E.Exp -> Span -> E.Exp
unOp op expr s = E.App s (E.Var (getSpan op) op) expr


leftSection :: Variable -> E.Exp -> Span -> FreestStateT E.Exp
leftSection op e s = do
  venv <- getVEnv
  i <- getNextIndex
  let v = mkNewVar i (mkVar s "_x")
  let t = genFstType (venv Map.! op)
  return $ E.Abs s Un (Bind s v t
             (E.App s (E.App s (E.Var (getSpan op) op) (E.Var (getSpan op) v)) e))
  where
    genFstType (T.Arrow _ _ t _) = t
    genFstType t = t

    
-- Datatypes

typeListsToUnArrows :: Variable -> [(Variable, [T.Type])] -> [(Variable, T.Type)]
typeListsToUnArrows a = 
  map \(c, ts) -> (c, foldr (T.Arrow (getSpan c) Un) (T.Var (getSpan a) a) ts)

insertMap :: Ord k => k -> [v] -> Map.Map k [v] -> Map.Map k [v]
insertMap = Map.insertWith (++)

condCase :: Span -> E.Exp -> E.Exp -> E.Exp -> E.Exp 
condCase s i t e = E.Case s i $ Map.fromList [(mkTrue  s, ([],t))
                                             ,(mkFalse s, ([],e))]
