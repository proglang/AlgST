{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}

module AlgST.Rename.Modules where

import AlgST.Syntax.Name
import AlgST.Util.Lenses
import Data.Generics.Lens.Lite
import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as HM
import GHC.Generics (Generic)
import Language.Haskell.TH.Syntax (Lift)
import Lens.Family2 (Lens')

-- | A map from module names to their top level definitions.
type Globals = HashMap ModuleName ModuleMap

-- | The top-level definitions in a module. This maps their unqualified name to
-- the globally-unique resolved name.
newtype TopLevels scope = TopLevels (HashMap Unqualified (NameR scope))
  deriving stock (Lift)

_TopLevels :: Lens' (TopLevels scope) (HashMap Unqualified (NameR scope))
_TopLevels = coerced
{-# INLINE _TopLevels #-}

-- | A @ModuleMap@ maps unqualified top level names of a module to the
-- corresponding globally-resolved name.
data ModuleMap = ModuleMap
  { modMapTypes :: !(TopLevels Types),
    modMapValues :: !(TopLevels Values)
  }
  deriving stock (Generic, Lift)

instance ScopeIndexed ModuleMap TopLevels where
  typesScopeL = field @"modMapTypes"
  valuesScopeL = field @"modMapValues"

emptyModuleMap :: ModuleMap
emptyModuleMap = ModuleMap (TopLevels HM.empty) (TopLevels HM.empty)
