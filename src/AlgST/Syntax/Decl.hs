{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module AlgST.Syntax.Decl where

import AlgST.Syntax.Expression qualified as E
import AlgST.Syntax.Kind qualified as K
import AlgST.Syntax.Name
import AlgST.Syntax.Phases
import AlgST.Syntax.Type qualified as T
import Control.Category ((>>>))
import Data.Functor.Identity
import Data.Kind qualified as Hs
import Data.Map.Strict qualified as Map
import Data.Maybe
import Data.Void
import Language.Haskell.TH.Syntax (Lift)
import Lens.Family2
import Lens.Family2.Unchecked (lens)

{- ORMOLU_DISABLE -}
type family XAliasDecl x
type family XDataDecl x
type family XProtocolDecl x

type family XDataCon x
type family XProtoCon x
{- ORMOLU_ENABLE -}

type ForallDeclX (c :: Hs.Type -> Hs.Constraint) x =
  ( c (XAliasDecl x),
    c (XDataDecl x),
    c (XProtocolDecl x)
  )

type ForallConX (c :: Hs.Type -> Hs.Constraint) x =
  ( c (XDataCon x),
    c (XProtoCon x)
  )

type ForallX (c :: Hs.Type -> Hs.Constraint) x =
  ( ForallConX c x,
    ForallDeclX c x
  )

data TypeAlias x = TypeAlias
  { aliasParams :: XParams x,
    aliasKind :: Maybe K.Kind,
    aliasType :: T.Type x
  }

deriving stock instance (T.ForallX Lift x) => Lift (TypeAlias x)

data TypeNominal stage c = TypeNominal
  { nominalParams :: Params stage,
    nominalKind :: K.Kind,
    nominalConstructors :: Constructors stage c
  }
  deriving (Lift)

type Params stage = [(Located (Name stage Types), K.Kind)]

type XParams x = Params (XStage x)

type Constructors stage a = NameMapG stage Values (Pos, [a])

mapConstructors ::
  (ProgVar stage -> a -> b) ->
  (Constructors stage a -> Constructors stage b)
mapConstructors f = runIdentity . traverseConstructors (\k -> Identity . f k)

traverseConstructors ::
  Applicative f =>
  (ProgVar stage -> a -> f b) ->
  (Constructors stage a -> f (Constructors stage b))
traverseConstructors f = Map.traverseWithKey (traverse . traverse . f)

data Origin
  = OriginUser !Pos
  | OriginImport !String
  | OriginBuiltin
  deriving (Lift)

instance HasPos Origin where
  pos = \case
    OriginUser p -> p
    _ -> ZeroPos

class Originated a where
  originL :: Lens' a Origin

instance Originated Origin where
  originL = id
  {-# INLINE originL #-}

instance Originated Void where
  originL = lens absurd const

instance (Originated a, Originated b) => Originated (Either a b) where
  originL f = either (fmap Left . originL f) (fmap Right . originL f)
  {-# INLINE originL #-}

-- | Checks for 'OriginBuiltin'.
isBuiltin :: Originated a => a -> Bool
isBuiltin =
  view originL >>> \case
    OriginBuiltin -> True
    _ -> False

originAt :: Originated a => a -> Pos -> a
originAt a p =
  a & originL %~ \case
    OriginUser _ -> OriginUser p
    origin -> origin

data TypeDecl x
  = AliasDecl (XAliasDecl x) (TypeAlias x)
  | DataDecl (XDataDecl x) (TypeNominal (XStage x) (T.Type x))
  | ProtoDecl (XProtocolDecl x) (TypeNominal (XStage x) (T.Type x))

deriving stock instance (ForallDeclX Lift x, T.ForallX Lift x) => Lift (TypeDecl x)

instance ForallDeclX Originated x => Originated (TypeDecl x) where
  originL f = \case
    AliasDecl x decl -> flip AliasDecl decl <$> originL f x
    DataDecl x decl -> flip DataDecl decl <$> originL f x
    ProtoDecl x decl -> flip ProtoDecl decl <$> originL f x
  {-# INLINE originL #-}

declParams :: TypeDecl x -> XParams x
declParams = \case
  AliasDecl _ alias -> aliasParams alias
  DataDecl _ decl -> nominalParams decl
  ProtoDecl _ decl -> nominalParams decl

declConstructors ::
  forall x.
  (XDataDecl x -> Pos -> XDataCon x) ->
  (XProtocolDecl x -> Pos -> XProtoCon x) ->
  XTypeVar x ->
  TypeDecl x ->
  NameMapG (XStage x) Values (ConstructorDecl x)
declConstructors xData xProto name d = case d of
  AliasDecl _ _ ->
    Map.empty
  DataDecl x decl -> do
    -- Falling back to 'Un' is not 100% correct but we know that for a well
    -- formed data declaration the kind *must* have multiplicity information.
    -- So the only way to get 'Nothing' here is when the user annotated the
    -- declaration to have kind 'P' which will lead to an erorr diagnosis.
    let mul = K.Un `fromMaybe` K.multiplicity (nominalKind decl)
    let con (p, items) = DataCon @x (xData x p) name (declParams d) mul items
    Map.map con (nominalConstructors decl)
  ProtoDecl x decl -> do
    let con (p, items) = ProtocolCon @x (xProto x p) name (declParams d) items
    Map.map con (nominalConstructors decl)

instance ForallDeclX HasPos x => HasPos (TypeDecl x) where
  pos = \case
    AliasDecl x _ -> pos x
    DataDecl x _ -> pos x
    ProtoDecl x _ -> pos x

data SignatureDecl x = SignatureDecl
  { signatureOrigin :: !Origin,
    signatureType :: T.Type x
  }

deriving stock instance (T.ForallX Lift x) => Lift (SignatureDecl x)

instance Originated (SignatureDecl x) where
  originL =
    lens
      (\(SignatureDecl origin _) -> origin)
      (\(SignatureDecl _ ty) origin -> SignatureDecl origin ty)

instance HasPos (SignatureDecl x) where
  pos = pos . view originL

data ValueDecl x = ValueDecl
  { valueOrigin :: Origin,
    valueType :: T.Type x,
    valueParams :: [Located (ANameG (XStage x))],
    valueBody :: E.Exp x
  }

deriving stock instance (E.ForallX Lift x, T.ForallX Lift x) => Lift (ValueDecl x)

instance Originated (ValueDecl x) where
  originL = lens valueOrigin \d origin ->
    d {valueOrigin = origin}
  {-# INLINE originL #-}

instance HasPos (ValueDecl x) where
  pos = pos . valueOrigin

valueSignatureDecl :: ValueDecl x -> SignatureDecl x
valueSignatureDecl = SignatureDecl <$> valueOrigin <*> valueType

data ConstructorDecl x
  = -- | A data constructor is annotated with
    --
    -- * the parent type's name
    -- * the parent type's parameters
    -- * the parent type's 'Multiplicity'
    -- * the constructor's items
    DataCon (XDataCon x) !(XTypeVar x) (XParams x) !K.Multiplicity [T.Type x]
  | -- | A protocol (non-data) constructor is annotated with
    --
    -- * the parent type's name
    -- * the parent type's parameters
    -- * the constructor's items
    ProtocolCon (XProtoCon x) !(XTypeVar x) (XParams x) [T.Type x]

deriving stock instance (ForallConX Lift x, T.ForallX Lift x) => Lift (ConstructorDecl x)

instance ForallConX Originated x => Originated (ConstructorDecl x) where
  originL f = \case
    DataCon x name params mul items -> do
      x' <- originL f x
      pure $ DataCon x' name params mul items
    ProtocolCon x name params items -> do
      x' <- originL f x
      pure $ ProtocolCon x' name params items
  {-# INLINE originL #-}

conParent :: ConstructorDecl x -> XTypeVar x
conParent = \case
  DataCon _ n _ _ _ -> n
  ProtocolCon _ n _ _ -> n

conParams :: ConstructorDecl x -> XParams x
conParams = \case
  DataCon _ _ ps _ _ -> ps
  ProtocolCon _ _ ps _ -> ps

conItems :: ConstructorDecl x -> [T.Type x]
conItems = \case
  DataCon _ _ _ _ ts -> ts
  ProtocolCon _ _ _ ts -> ts

instance ForallConX HasPos x => HasPos (ConstructorDecl x) where
  pos = \case
    DataCon x _ _ _ _ -> pos x
    ProtocolCon x _ _ _ -> pos x
