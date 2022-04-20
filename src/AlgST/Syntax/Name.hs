{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module AlgST.Syntax.Name
  ( -- * Names
    Name (..),
    pattern Global,
    isGlobal,
    pattern Local,
    isLocal,

    -- ** Abbreviations
    ProgVar,
    TypeVar,

    -- ** Pretty-printing
    pprName,

    -- * Modules
    Module,
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
import Data.Hashable
import Data.Kind
import Data.List qualified as List
import Data.Maybe
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

type Name :: Scope -> Type
data Name scope = Name
  { nameModule :: Maybe Module,
    nameUnqualified :: String
  }
  deriving stock (Eq, Ord, Show, Generic, Lift)

instance Hashable (Name scope)

pattern Local :: String -> Name scope
pattern Local s = Name {nameModule = Nothing, nameUnqualified = s}

pattern Global :: Module -> String -> Name scope
pattern Global m s = Name {nameModule = Just m, nameUnqualified = s}

{-# COMPLETE Global, Local #-}

isGlobal :: Name scope -> Bool
isGlobal Global {} = True
isGlobal _ = False

isLocal :: Name scope -> Bool
isLocal = not . isGlobal

pprName :: Name scope -> String
pprName n =
  List.intercalate "." . catMaybes $
    [ moduleName <$> nameModule n,
      Just (nameUnqualified n)
    ]
