{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}

module G2.Language.PolyArgMap ( PolyArgMap
                               , insertEmpty
                               , insert
                               , lookup
                               , remove 
                               , toList ) where 

import G2.Language.Syntax

import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import Data.Data (Data, Typeable)
import Data.Hashable(Hashable)
import GHC.Generics (Generic)
import Prelude hiding (lookup)

-- | Interface for the PAM
newtype PolyArgMap = PolyArgMap (HM.HashMap Id (HS.HashSet Id)) deriving (Show, Eq, Read, Data, Typeable, Generic)

insertEmpty :: Id -> PolyArgMap -> PolyArgMap
insertEmpty i (PolyArgMap pargm) = if not $ HM.member i pargm then PolyArgMap $ HM.insert i HS.empty pargm
                                else error "PolyArgMap.insertEmpty: inserting empty mapping for already existing tyVar"

insert :: Id -> Id -> PolyArgMap -> PolyArgMap
insert tv lv (PolyArgMap pargm) = if HM.member tv pargm then PolyArgMap $ HM.adjust (HS.insert lv) tv pargm
                                else  error "PolyArgMap.insert: trying to into set of TyVar not in map"

lookup :: Id -> PolyArgMap -> Maybe [Id]
lookup tv (PolyArgMap pargm) = case HM.lookup tv pargm of
                    Just ns -> Just (HS.toList ns)
                    Nothing -> Nothing

remove :: Id -> PolyArgMap -> PolyArgMap
remove i (PolyArgMap pargm) = let pargm' = HM.delete i pargm in 
            if pargm == pargm' 
            then error "PolyArgMap.remove: removing nonexistent TV"  
            else PolyArgMap $ pargm'

toList :: PolyArgMap -> [(Id, HS.HashSet Id)]
toList (PolyArgMap pargm) = HM.toList pargm

instance Hashable PolyArgMap