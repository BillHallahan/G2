{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}

module G2.Language.PolyArgMap ( PolyArgMap
                               , insertEmpty
                               , insert
                               , lookup
                               , remove 
                               , toList
                               , empty ) where 

import G2.Language.Syntax
import qualified G2.Language.Naming as N

import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import qualified Data.Sequence as S
import Data.Data (Data, Typeable)
import Data.Hashable(Hashable)
import GHC.Generics (Generic)
import Prelude hiding (lookup)
import Debug.Trace

-- | Interface for the PAM
newtype PolyArgMap = PolyArgMap (HM.HashMap Name (HS.HashSet Name)) deriving (Show, Eq, Read, Data, Typeable, Generic)

insertEmpty :: Name -> PolyArgMap -> PolyArgMap
insertEmpty i (PolyArgMap pargm) = if not $ HM.member i pargm then PolyArgMap $ HM.insert i HS.empty pargm
                                else error "PolyArgMap.insertEmpty: inserting empty mapping for already existing tyVar"

insert :: Name -> Name -> PolyArgMap -> PolyArgMap
insert tv lv (PolyArgMap pargm) = if HM.member tv pargm then PolyArgMap $ HM.adjust (HS.insert lv) tv pargm
                                else  error "PolyArgMap.insert: trying to into set of TyVar not in map"

lookup :: Name -> PolyArgMap -> Maybe [Name]
lookup tv (PolyArgMap pargm) = case HM.lookup tv pargm of
                    Just ns -> Just (HS.toList ns)
                    Nothing -> Nothing

remove :: Name -> PolyArgMap -> PolyArgMap
remove i (PolyArgMap pargm) = let pargm' = HM.delete i pargm in 
            if pargm == pargm' 
            then error "PolyArgMap.remove: removing nonexistent TV"  
            else PolyArgMap $ pargm'

toList :: PolyArgMap -> [(Name, HS.HashSet Name)]
toList (PolyArgMap pargm) = HM.toList pargm

empty :: PolyArgMap
empty = PolyArgMap HM.empty

instance Hashable PolyArgMap

instance N.Named PolyArgMap where  
    names (PolyArgMap pargm) = S.fromList $ foldr ((\(ty, args) y -> (HS.toList args) ++ (ty:y))) [] (HM.toList pargm) -- TODO: untested
    rename old new pam@(PolyArgMap pargm) = case lookup old pam of
                    Just ns -> PolyArgMap $ HM.insert new (HS.fromList ns) (HM.delete old pargm) -- name is key
                    Nothing -> PolyArgMap $ HM.map (HS.map (\y -> if y==old then new else y)) pargm -- name is value
    renames hm pargm = go (HM.toList hm) pargm
                            where
                                go :: [(Name, Name)] -> PolyArgMap -> PolyArgMap
                                go ((old, new):rns) pargm_ = go rns (N.rename old new pargm_)
                                go [] pargm_ = pargm_