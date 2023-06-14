module G2.Language.TypeClasses.Extra ( eqTCDict
                                     , numTCDict
                                     , ordTCDict
                                     , integralTCDict ) where

import G2.Language.KnownValues
import G2.Language.Syntax
import G2.Language.TypeClasses.TypeClasses
import G2.Language.Typing

import Data.List
import Data.Maybe

eqTCDict :: KnownValues -> TypeClasses -> Type -> Maybe Id
eqTCDict kv tc t = lookupTCDict tc (eqTC kv) t

numTCDict :: KnownValues -> TypeClasses -> Type -> Maybe Id
numTCDict kv tc t = lookupTCDict tc (numTC kv) t

ordTCDict :: KnownValues -> TypeClasses -> Type -> Maybe Id
ordTCDict kv tc t = lookupTCDict tc (ordTC kv) t

integralTCDict :: KnownValues -> TypeClasses -> Type -> Maybe Id
integralTCDict kv tc t = lookupTCDict tc (integralTC kv) t