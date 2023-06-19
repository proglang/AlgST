{-# LANGUAGE FlexibleInstances #-}
module Util.GetTOps
  ( DefaultTypeOp(..)
  )
where

import           Data.Bifunctor                 ( second )
import qualified Data.Map.Strict               as Map
import           Data.Maybe                     ( fromMaybe )
import           Parse.Unparser                 ( )
import           Syntax.Base
import           Syntax.Expression
import qualified Syntax.Kind                   as K
import           Syntax.Program
import qualified Syntax.Type                   as T

-- | Class to get the type operators back to their original locations

class DefaultTypeOp a where
  getDefault :: TypeOpsEnv -> a -> a

instance DefaultTypeOp T.Type where
  getDefault m (T.Arrow p mu t u) =
    lookupPos m p $ T.Arrow p mu (getDefault m t) (getDefault m u)
  getDefault m (T.Labelled p s cm) =
    lookupPos m p $ T.Labelled p s $ getDefault m cm
  getDefault m (T.Semi p t u) =
    lookupPos m p $ T.Semi p (getDefault m t) (getDefault m u)
  getDefault m (T.Message p pol t) =
    lookupPos m p $ T.Message p pol $ getDefault m t
  getDefault m (T.Forall p b) = lookupPos m p $ T.Forall p $ getDefault m b
  getDefault m (T.Rec    p b) = lookupPos m p $ T.Rec p $ getDefault m b
  getDefault _ t              = t

instance DefaultTypeOp Exp where
  getDefault m (Abs p mul b   ) = Abs p mul $ getDefault m b
  getDefault m (App  p e1 e2) = App p (getDefault m e1) (getDefault m e2)
  getDefault m (BinLet p x y e1 e2) =
    BinLet p x y (getDefault m e1) (getDefault m e2)
  getDefault m (Case p e fm  ) = Case p (getDefault m e) (getDefault m fm)
  getDefault m (TypeAbs p b  ) = TypeAbs p $ getDefault m b
  getDefault m (TypeApp p e t) = TypeApp p (getDefault m e) (getDefault m t)
  getDefault m (Cond p e1 e2 e3) =
    Cond p (getDefault m e1) (getDefault m e2) (getDefault m e3)
  getDefault m (UnLet p x e1 e2) =
    UnLet p x (getDefault m e1) (getDefault m e2)
  getDefault _ e           = e

instance DefaultTypeOp (Bind K.Kind Exp) where
  getDefault m (Bind p x k e) = Bind p x k $ getDefault m e

instance DefaultTypeOp (Bind T.Type Exp) where
  getDefault m (Bind p x k t) = Bind p x k $ getDefault m t

instance DefaultTypeOp FieldMap where
  getDefault m = Map.map $ second (getDefault m) -- (\(x, y) -> (x, getDefault m y))

instance DefaultTypeOp (Bind K.Kind T.Type) where
  getDefault m (Bind p x k t) = Bind p x k $ getDefault m t

instance DefaultTypeOp T.TypeMap where
  getDefault m = Map.map (getDefault m)

lookupPos :: TypeOpsEnv -> Span -> T.Type -> T.Type
lookupPos tops p defaultType = fromMaybe defaultType (tops Map.!? p)
