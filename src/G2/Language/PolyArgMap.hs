{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}

module G2.Language.PolyArgMap ( PolyArgMap
                               , LamRename (..)
                               , insertEmpty
                               , insert
                               , lookup
                               , member
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
import Data.Maybe (isJust)

-- | Interface for the PAM
data LamRename = LamRename {lam :: Name, rename :: Name} deriving (Show, Eq, Read, Data, Typeable, Generic)
newtype PolyArgMap = PolyArgMap (HM.HashMap Name (HS.HashSet LamRename)) deriving (Show, Eq, Read, Data, Typeable, Generic)

insertEmpty :: Name -> PolyArgMap -> PolyArgMap
insertEmpty i (PolyArgMap pargm) = if not $ HM.member i pargm then PolyArgMap $ HM.insert i HS.empty pargm
                                else error "PolyArgMap.insertEmpty: inserting empty mapping for already existing tyVar"

insert :: Name -> LamRename -> PolyArgMap -> PolyArgMap
insert tv lr (PolyArgMap pargm) = if HM.member tv pargm then PolyArgMap $ HM.adjust (HS.insert lr) tv pargm
                                else  error "PolyArgMap.insert: trying to into set of TyVar not in map"

lookup :: Name -> PolyArgMap -> Maybe [LamRename]
lookup tv (PolyArgMap pargm) = case HM.lookup tv pargm of
                    Just lrs -> Just (HS.toList lrs)
                    Nothing -> Nothing

member :: Name -> PolyArgMap -> Bool
member n pam = isJust (lookup n pam)

remove :: Name -> PolyArgMap -> PolyArgMap
remove i (PolyArgMap pargm) = let pargm' = HM.delete i pargm in 
            if pargm == pargm' 
            then error "PolyArgMap.remove: removing nonexistent TV"  
            else PolyArgMap $ pargm'

toList :: PolyArgMap -> [(Name, HS.HashSet LamRename)]
toList (PolyArgMap pargm) = HM.toList pargm

empty :: PolyArgMap
empty = PolyArgMap HM.empty

instance Hashable PolyArgMap
instance Hashable LamRename

instance N.Named PolyArgMap where  
    names (PolyArgMap pargm) = S.fromList $ foldr ((\(ty, lrs) y -> (lrExpand lrs) ++ (ty:y))) [] (HM.toList pargm) -- TODO: untested
                                        where lrExpand :: HS.HashSet LamRename -> [Name]
                                              lrExpand lrs = foldr (\(LamRename l r) xs -> l:r:xs) [] (HS.toList lrs)
    rename old new pam@(PolyArgMap pargm) = case lookup old pam of
                    Just ns -> PolyArgMap $ HM.insert new (HS.fromList ns) (HM.delete old pargm) -- name is key
                    Nothing -> PolyArgMap $ HM.map (HS.map renameLR) pargm -- name is value
                    where 
                        renameLR :: LamRename -> LamRename
                        renameLR (LamRename l r) = LamRename (if l == old then new else l) (if r == old then new else r)
    renames hm pargm = go (HM.toList hm) pargm
                            where
                                go :: [(Name, Name)] -> PolyArgMap -> PolyArgMap
                                go ((old, new):rns) pargm_ = go rns (N.rename old new pargm_)
                                go [] pargm_ = pargm_