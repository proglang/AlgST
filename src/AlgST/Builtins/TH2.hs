{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fno-defer-type-errors #-}

module AlgST.Builtins.TH2
  ( -- * Generating resolved top-level names.
    Defines,
    runDefines,
    defineType,
    defineValue,
    defineOperator,
  )
where

import AlgST.Rename.Fresh
import AlgST.Rename.Modules
import AlgST.Syntax.Name as Syn
import AlgST.Syntax.Operators
import AlgST.Util.Lenses
import Control.Monad
import Control.Monad.Trans.Class qualified as T
import Control.Monad.Trans.Writer.CPS
import Data.Coerce
import Data.DList qualified as DL
import Data.Foldable
import Data.Functor.Compose
import Data.HashMap.Strict qualified as HM
import Data.Singletons
import Data.Traversable
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
                DL.DList (NameR Values, (Precedence, Associativity)),
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

defineType :: String -> Unqualified -> Defines ()
defineType = fmap void . define STypes [t|Syn.Name Resolved Types|] . Just

defineValue :: String -> Unqualified -> Defines ()
defineValue = fmap void . define SValues [t|Syn.Name Resolved Values|] . Just

defineOperator :: Maybe String -> Unqualified -> Associativity -> Precedence -> Defines ()
defineOperator symName unq assoc prec = do
  resolved <- define SValues [t|Syn.Name Resolved Values|] symName unq
  Defines $ T.lift $ tell (mempty, DL.singleton (resolved, (prec, assoc)), mempty)

define ::
  Sing (scope :: Scope) ->
  Q TH.Type ->
  Maybe String ->
  Unqualified ->
  Defines (NameR scope)
define ss symType mName unq = Defines do
  resolved <- freshResolved $ Name emptyModuleName unq
  symDecs <- for mName \symName -> do
    symSig <- T.lift . T.lift $ sigD (mkName symName) symType
    symDef <- T.lift . T.lift $ simpleFunD (mkName symName) (TH.lift resolved)
    pure $ DL.fromList [symSig, symDef]
  let builtinDef = BuiltinDef (unq, resolved)
      registry =
        scopedVariants (Compose DL.empty)
          & scopeL' ss . coercedFrom Compose .~ DL.singleton builtinDef
  T.lift $ tell (fold symDecs, mempty, registry)
  pure resolved

runDefines :: ModuleName -> String -> String -> Defines () -> DecsQ
runDefines modName mapSym opsSym (Defines defs) = do
  (symDecs, ops, defs) <- execWriterT (runFreshT modName defs)
  let moduleMap = builtinDefsToModuleMap defs
  modMapDef <-
    simpleFunD
      (mkName mapSym)
      (TH.lift moduleMap)
  opsTableDef <-
    simpleFunD
      (mkName opsSym)
      [|HM.fromList $(TH.lift (DL.toList ops)) :: OperatorTable|]
  pure $ modMapDef : opsTableDef : DL.toList symDecs

simpleFunD :: Quote m => TH.Name -> m Exp -> m Dec
simpleFunD name body = funD name [clause [] (normalB body) []]

builtinDefsToModuleMap :: ScopedVariants (Compose DL.DList BuiltinDef) -> ModuleMap
builtinDefsToModuleMap (coerce -> typDefs, coerce -> valDefs) =
  ModuleMap
    { modMapTypes = TopLevels $ HM.fromList $ DL.toList typDefs,
      modMapValues = TopLevels $ HM.fromList $ DL.toList valDefs
    }
