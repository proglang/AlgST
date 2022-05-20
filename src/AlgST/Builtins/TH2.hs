{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
{-# LANGUAGE ViewPatterns #-}

module AlgST.Builtins.TH2
  ( -- * Generating resolved top-level names.
    Defines,
    runDefines,
    defineType,
    defineValue,
    defineTypeU,
    defineValueU,
  )
where

import AlgST.Rename.Fresh
import AlgST.Rename.Modules
import AlgST.Syntax.Name as Syn
import AlgST.Util.Lenses
import Control.Monad.Trans.Class qualified as T
import Control.Monad.Trans.Writer.CPS
import Data.Coerce
import Data.DList qualified as DL
import Data.Functor.Compose
import Data.HashMap.Strict qualified as HM
import Data.Singletons
import Language.Haskell.TH
import Language.Haskell.TH qualified as TH
import Language.Haskell.TH.Syntax qualified as TH
import Lens.Family2

newtype BuiltinDef scope = BuiltinDef (Unqualified, NameR scope)

newtype Defines a
  = Defines
      ( FreshT
          ( WriterT
              ( DL.DList Dec,
                ScopedVariants (Compose DL.DList BuiltinDef)
              )
              Q
          )
          a
      )
  deriving newtype (Functor, Applicative, Monad)

#if !MIN_VERSION_base(4, 16, 0)
-- These instances are provided starting with base 4.16.0.0. Just derive them
-- if were using an earlier version.
deriving newtype instance Semigroup (f (g a)) => Semigroup (Compose f g a)
deriving newtype instance Monoid (f (g a)) => Monoid (Compose f g a)
#endif

defineTypeU :: String -> String -> Defines ()
defineTypeU = coerce defineType

defineValueU :: String -> String -> Defines ()
defineValueU = coerce defineValue

defineType :: String -> Unqualified -> Defines ()
defineType = define STypes [t|Syn.Name Resolved Types|]

defineValue :: String -> Unqualified -> Defines ()
defineValue = define SValues [t|Syn.Name Resolved Values|]

define :: Sing (scope :: Scope) -> Q TH.Type -> String -> Unqualified -> Defines ()
define ss symType symName unq = Defines do
  resolved <- freshResolved $ Name emptyModuleName unq
  symSig <- T.lift . T.lift $ sigD (mkName symName) symType
  symDef <- T.lift . T.lift $ simpleFunD (mkName symName) (TH.lift resolved)
  let builtinDef = BuiltinDef (unq, resolved)
      registry =
        scopedVariants (Compose DL.empty)
          & scopeL' ss . coercedFrom Compose .~ DL.singleton builtinDef
  T.lift $ tell (DL.fromList [symSig, symDef], registry)

runDefines :: ModuleName -> String -> Defines () -> DecsQ
runDefines modName mapSym (Defines defs) = do
  (decs, defs) <- execWriterT (runFreshT modName defs)
  let moduleMap = builtinDefsToModuleMap defs
  modMapSig <- sigD (mkName mapSym) [t|ModuleMap|]
  modMapDef <- simpleFunD (mkName mapSym) (TH.lift moduleMap)
  pure $ modMapSig : modMapDef : DL.toList decs

simpleFunD :: Quote m => TH.Name -> m Exp -> m Dec
simpleFunD name body = funD name [clause [] (normalB body) []]

builtinDefsToModuleMap :: ScopedVariants (Compose DL.DList BuiltinDef) -> ModuleMap
builtinDefsToModuleMap (coerce -> typDefs, coerce -> valDefs) =
  ModuleMap
    { modMapTypes = TopLevels $ HM.fromList $ DL.toList typDefs,
      modMapValues = TopLevels $ HM.fromList $ DL.toList valDefs
    }
