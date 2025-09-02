{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}

module G2.Language.PolyArgMap ( PolyArgMap
                               , insertTV
                               , insertRename
                               , lookup
                               , member
                               , remove
                               , toList
                               , empty ) where

import G2.Language.Syntax
import qualified G2.Language.Naming as N

import qualified Data.HashMap.Lazy as HM
import qualified Data.Sequence as S
import Data.Data (Data, Typeable)
import Data.Hashable(Hashable)
import GHC.Generics (Generic)
import Prelude hiding (lookup)
import Data.Maybe (isJust)

-- | Interface for the PAM
newtype PolyArgMap = PolyArgMap (HM.HashMap Name (HM.HashMap Name Name)) deriving (Show, Eq, Read, Data, Typeable, Generic)

insertTV :: Name -> PolyArgMap -> PolyArgMap
insertTV tv pam@(PolyArgMap pargm)
    | not $ member tv pam = PolyArgMap $ HM.insert tv HM.empty pargm
    | otherwise = error "PolyArgMap.insertTV: inserting empty mapping for already existing tyVar"

insertRename :: Name -> Name -> Name -> PolyArgMap -> PolyArgMap
insertRename tv l r (PolyArgMap pargm) | Just hm <- HM.lookup tv pargm =
    PolyArgMap $ HM.insert tv (HM.insert l r hm) pargm
  | otherwise = error "PolyArgMap.insertRename: trying to into set of TyVar not in map"

lookup :: Name -> PolyArgMap -> Maybe [(Name, Name)]
lookup tv (PolyArgMap pargm) = case HM.lookup tv pargm of
                    Just lrs -> Just (HM.toList lrs)
                    Nothing -> Nothing

member :: Name -> PolyArgMap -> Bool
member n pam = isJust (lookup n pam)

remove :: Name -> PolyArgMap -> PolyArgMap
remove i (PolyArgMap pargm) = let pargm' = HM.delete i pargm in
            if pargm == pargm'
            then error "PolyArgMap.remove: removing nonexistent TV"
            else PolyArgMap pargm'

toList :: PolyArgMap -> [(Name, [(Name, Name)])]
toList (PolyArgMap pargm) = map (\(tv, rns) -> (tv, HM.toList rns)) (HM.toList pargm)

empty :: PolyArgMap
empty = PolyArgMap HM.empty

instance Hashable PolyArgMap

instance N.Named PolyArgMap where
    names (PolyArgMap pargm) = S.fromList $ foldr (\(ty, lrs) y -> lrExpand lrs ++ (ty:y)) [] (HM.toList pargm) -- TODO: untested
                                        where lrExpand :: HM.HashMap Name Name -> [Name]
                                              lrExpand lrs = foldr (\(l, r) xs -> l:r:xs) [] (HM.toList lrs)
    rename old new pam@(PolyArgMap pargm) = case lookup old pam of
                    Just ns -> PolyArgMap $ HM.insert new (HM.fromList ns) (HM.delete old pargm) -- name is key
                    Nothing -> PolyArgMap $ HM.map (HM.fromList . map renameLR . HM.toList) pargm -- name is value
                    where
                        renameLR :: (Name, Name) -> (Name, Name)
                        renameLR (l, r) = (if l == old then new else l, if r == old then new else r)
    renames hm pargm = go (HM.toList hm) pargm
                            where
                                go :: [(Name, Name)] -> PolyArgMap -> PolyArgMap
                                go ((old, new):rns) pargm_ = go rns (N.rename old new pargm_)
                                go [] pargm_ = pargm_