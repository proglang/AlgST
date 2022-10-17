{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module AlgST.Typing.Variables
  ( -- * General
    useVar,

    -- * Implicits
    QueryM,
    runQuery,
    queryImplicit,
    eliminateImplicits,
  )
where

import AlgST.Syntax.Decl qualified as D
import AlgST.Syntax.Destructure qualified as Ds
import AlgST.Syntax.Expression qualified as E
import AlgST.Syntax.Name
import AlgST.Syntax.Pos
import AlgST.Syntax.Type qualified as T
import AlgST.Typing.Error qualified as Error
import AlgST.Typing.Monad
import AlgST.Typing.NormalForm
import AlgST.Typing.Phase
import AlgST.Typing.Subtyping (Alpha (..))
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Validate
import Data.Foldable
import Data.Map qualified as Map
import Data.Maybe
import Lens.Family2.State
import Lens.Family2.Stock qualified as L

useVar :: MonadValidate Errors m => Pos -> ProgVar TcStage -> Var -> m Var
useVar loc name v = case varUsage v of
  UnUsage ->
    pure v
  LinUnunsed ->
    pure v {varUsage = LinUsed loc}
  LinUsed ppos -> do
    Error.add (Error.linVarUsedTwice ppos loc name v)
    pure v

type Implicit = (ProgVar TcStage, TcType, Maybe Var)

newtype QueryM a = QueryM (ReaderT [Implicit] TypeM a)
  deriving newtype (Functor, Applicative, Monad)
  deriving newtype (MonadReader [Implicit])
  deriving newtype (MonadState TySt)
  deriving newtype (MonadValidate Errors)

runQuery :: QueryM a -> TypeM a
runQuery (QueryM m) = allImplicits >>= runReaderT m

queryImplicit :: Pos -> TcType -> QueryM TcExp
queryImplicit loc ty = do
  candidates <- asks $ mapMaybe $ checkCandidate loc ty
  case candidates of
    [(build, _)] -> build
    [] -> Error.fatal $ Error.noImplicitFound loc ty (nf ty)
    _ -> Error.fatal $ Error.manyImplicitsFound loc ty (snd <$> candidates)

checkCandidate :: Pos -> TcType -> Implicit -> Maybe (QueryM TcExp, (ProgVar TcStage, Maybe Pos))
checkCandidate loc target (n, ty, mvar) = do
  let candTy = dropImplicitArgs ty
  targetNF <- nf target
  candNF <- nf candTy
  guard $ Alpha candNF <= Alpha targetNF
  pure
    let builder = do
          for_ mvar \var -> do
            var' <- useVar loc n var
            tcTypeEnvL . L.at' n .= Just var'
          fst <$> eliminateImplicits (E.Var loc n) ty
     in (builder, (n, pos <$> mvar))

dropImplicitArgs :: TcType -> TcType
dropImplicitArgs = go
  where
    go (Ds.Arrow T.Implicit _ _ u) = dropImplicitArgs u
    go t = t

eliminateImplicits :: TcExp -> TcType -> QueryM (TcExp, TcType)
eliminateImplicits e (Ds.Arrow T.Implicit _ t u) = do
  tVal <- queryImplicit (pos e) t
  eliminateImplicits (E.App (pos e) e tVal) u
eliminateImplicits e ty = pure (e, ty)

-- | Returns the list of all implicits in scope.
allImplicits :: TypeM [(ProgVar TcStage, TcType, Maybe Var)]
allImplicits = do
  locals <- gets tcTypeEnv
  globals <- asks tcCheckedValues
  pure $ mapMaybe checkLocal (Map.toList locals) ++ mapMaybe checkGlobal (Map.toList globals)
  where
    checkLocal (n, v) = do
      guard $ varSpecific v == T.Implicit
      pure (n, varType v, Just v)
    checkGlobal (n, g) = do
      ValueGlobal (Just decl) ty <- pure g
      guard $ D.valueSpecificity decl == T.Implicit
      pure (n, ty, Nothing)
