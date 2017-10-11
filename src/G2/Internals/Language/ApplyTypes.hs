module G2.Internals.Language.ApplyTypes ( ApplyTypes
                                        , lookup
                                        , applyTypeName
                                        , applyTypeFunc
                                        , empty
                                        , insert
                                        , toList) where

import G2.Internals.Language.Naming
import G2.Internals.Language.Syntax

import Data.Coerce
import qualified Data.Map as M
import Prelude hiding (lookup)

newtype ApplyTypes = ApplyTypes (M.Map Type (Name, Id))
                     deriving (Show, Eq, Read)

applyTypesMap :: ApplyTypes -> M.Map Type (Name, Id)
applyTypesMap = coerce

lookup :: Type -> ApplyTypes -> Maybe (Name, Id)
lookup t = M.lookup t . applyTypesMap

applyTypeName :: Type -> ApplyTypes -> Maybe Name
applyTypeName t = fmap fst . lookup t

applyTypeFunc :: Type -> ApplyTypes -> Maybe Id
applyTypeFunc t = fmap snd . lookup t

empty :: ApplyTypes
empty = ApplyTypes M.empty

insert :: Type -> Name -> Id -> ApplyTypes -> ApplyTypes
insert t name funcName = coerce . M.insert t (name, funcName) . applyTypesMap

toList :: ApplyTypes -> [(Type, (Name, Id))]
toList = M.toList . applyTypesMap

instance Named ApplyTypes where
    names (ApplyTypes m) = names m

    rename old new (ApplyTypes m) = ApplyTypes $ rename old new m