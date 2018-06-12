module G2.Internals.Language.ApplyTypes ( ApplyTypes
                                        , lookup
                                        , applyTypeName
                                        , applyTypeFunc
                                        , applyFuncs
                                        , empty
                                        , insert
                                        , toList) where

import G2.Internals.Language.Naming
import G2.Internals.Language.Syntax

import Data.Coerce
import qualified Data.HashMap.Lazy as HM
import Prelude hiding (lookup)

newtype ApplyTypes = ApplyTypes (HM.HashMap Type (Name, Id))
                     deriving (Show, Eq, Read)

applyTypesMap :: ApplyTypes -> HM.HashMap Type (Name, Id)
applyTypesMap = coerce

lookup :: Type -> ApplyTypes -> Maybe (Name, Id)
lookup t = HM.lookup t . applyTypesMap

applyTypeName :: Type -> ApplyTypes -> Maybe Name
applyTypeName t = fmap fst . lookup t

applyTypeFunc :: Type -> ApplyTypes -> Maybe Id
applyTypeFunc t = fmap snd . lookup t

applyFuncs :: ApplyTypes -> [Id]
applyFuncs = map snd . HM.elems . applyTypesMap

empty :: ApplyTypes
empty = ApplyTypes HM.empty

insert :: Type -> Name -> Id -> ApplyTypes -> ApplyTypes
insert t name fn = coerce . HM.insert t (name, fn) . applyTypesMap

toList :: ApplyTypes -> [(Type, (Name, Id))]
toList = HM.toList . applyTypesMap

instance Named ApplyTypes where
    names (ApplyTypes m) = names m

    rename old new (ApplyTypes m) = ApplyTypes $ rename old new m