{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}

module G2.Language.PolyArgMap ( PolyArgMap
                               , insertTV
                               , insertRename
                               , lookup
                               , member
                               , remove
                               , toList
                               , fromList
                               , empty ) where

import G2.Language.Syntax

import qualified Data.HashMap.Lazy as HM
import Data.Data (Data, Typeable)
import Data.Hashable(Hashable)
import Data.Bifunctor
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
toList (PolyArgMap pargm) = map (second HM.toList) (HM.toList pargm)

fromList :: [(Name, [(Name, Name)])] -> PolyArgMap
fromList l = PolyArgMap . HM.fromList $ map (second HM.fromList) l

empty :: PolyArgMap
empty = PolyArgMap HM.empty

instance Hashable PolyArgMap
