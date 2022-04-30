{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module AlgST.Syntax.Name
  ( -- * Type/Value Names
    Name (..),
    pattern Wildcard,
    isWild,
    pattern PairCon,

    -- ** Abbreviations
    ProgVar,
    TypeVar,
    NameMap,
    NameSet,

    -- ** Unscoped Names
    AName,
    ANameMap,
    ANameSet,
    ANameLike (..),
    liftName,
    liftNameSet,
    liftNameMap,
    eitherName,

    -- ** Pretty-printing
    pprName,

    -- * Modules
    Module (..),
    moduleName,
    modulePath,
    moduleFromPath,

    -- * Type Level Tags
    Scope (..),
    SScope (..),
    TypesSym0,
    ValuesSym0,
  )
where

import Control.Category ((>>>))
import Control.Monad
import Data.Foldable
import Data.Hashable
import Data.Kind
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Singletons.TH
import GHC.Generics (Generic)
import Language.Haskell.TH.Syntax (Lift)
import System.FilePath qualified as FP

-- | The name of a module.
newtype Module = Module String
  deriving stock (Show, Lift)
  deriving newtype (Eq, Ord, Hashable)

moduleName :: Module -> String
moduleName (Module s) = s

modulePartSeparator :: Char
modulePartSeparator = '.'

-- | Produces the path under which the source code for the given module is
-- expected.
--
-- >>> modulePath (Module "Data.List")
-- "Data/List.algst"
modulePath :: Module -> FilePath
modulePath = moduleName >>> map adjustSep >>> flip FP.addExtension "algst"
  where
    adjustSep c
      | c == modulePartSeparator = FP.pathSeparator
      | otherwise = c

-- | Transforms a 'FilePath' to the corresponding 'Module'.
--
-- >>> moduleFromPath "Data/List.algst"
-- Module "Data.List"
--
-- Any extensions on the last component will be dropped. No further cleaning of
-- paths or validity checking will be performed. This can lead to invalid
-- module names:
--
-- >>> moduleFromPath "../Data.ext/List.algst"
-- Module "...Data.ext.List"
moduleFromPath :: FilePath -> Module
moduleFromPath = FP.dropExtensions >>> map adjustSep >>> Module
  where
    adjustSep c
      | FP.isPathSeparator c = modulePartSeparator
      | otherwise = c

-- | Type level tag to differentiate between type level and value level names.
data Scope = Types | Values
  deriving (Eq, Ord, Generic)

instance Hashable Scope

$(genSingletons [''Scope])

type ProgVar = Name Values

type TypeVar = Name Types

-- | TODO: Describe why every name has a module
--
-- > data T a = T a
--
-- > foo : forall (a:TU). ...
-- > foo [a] =
-- >  let x = T [a -> a] in
-- >  ...
--
-- @x@ has type @...@ but it should look like @...@
type Name :: Scope -> Type
data Name scope = Name
  { nameModule :: Module,
    nameUnqualified :: String
  }
  deriving stock (Eq, Ord, Show, Generic, Lift)

instance Hashable (Name scope)

pattern Wildcard :: Name scope
pattern Wildcard =
  Name
    { nameModule = Module "",
      nameUnqualified = "_"
    }

pattern PairCon :: Name scope
pattern PairCon =
  Name
    { nameModule = Module "",
      nameUnqualified = "(,)"
    }

-- | Checks wether the given name is a wildcard pattern.
isWild :: Name scope -> Bool
isWild Wildcard = True
isWild _ = False

pprName :: Name scope -> String
pprName n = fold modulePrefix ++ nameUnqualified n
  where
    modulePrefix :: Maybe String
    modulePrefix = do
      guard $ not $ isWild n
      guard $ not $ null $ moduleName $ nameModule n
      pure $ moduleName (nameModule n) ++ "."

-- TODO: Check if there is difference in runtime/allocation when switching
-- between ordered and unorderered maps.

type NameMap s = Map.Map (Name s)

type NameSet s = Set.Set (Name s)

type AName = Either TypeVar ProgVar

-- | A map which can have type and value names as its keys.
type ANameMap = Map.Map AName

-- | A set which can contain type and value names.
type ANameSet = Set.Set AName

class ANameLike name where
  foldName :: (TypeVar -> a) -> (ProgVar -> a) -> name -> a

instance SingI s => ANameLike (Name s) where
  foldName f g n = eitherName @s (f n) (g n)

instance ANameLike AName where
  foldName = either

eitherName :: forall s a. SingI s => (s ~ Types => a) -> (s ~ Values => a) -> a
eitherName tv pv = case sing @s of
  STypes -> tv
  SValues -> pv

liftName :: ANameLike name => name -> AName
liftName = foldName Left Right

liftNameSet :: SingI s => NameSet s -> ANameSet
liftNameSet = Set.mapMonotonic liftName

liftNameMap :: SingI s => NameMap s v -> ANameMap v
liftNameMap = Map.mapKeysMonotonic liftName
