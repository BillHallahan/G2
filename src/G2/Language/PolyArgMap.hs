{-# LANGUAGE DeriveDataTypeable, DeriveGeneric, LambdaCase #-}

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
import Data.List (find)
import Data.Bifunctor (second)
import GHC.Generics (Generic)
import Prelude hiding (lookup)
import Data.Maybe (isJust)

-- | Interface for the PAM

-- If the name is a val of the TV type, we already know it's type.
data ValOrFunc = Val | Func Type deriving (Show, Eq, Read, Data, Typeable, Generic)
data PAMEntry = PAMEntry {envN :: Name, runN :: Name, vOrF :: ValOrFunc} deriving (Show, Eq, Read, Data, Typeable, Generic)
newtype PolyArgMap = PolyArgMap (HM.HashMap Name [PAMEntry]) deriving (Show, Eq, Read, Data, Typeable, Generic)

insertTV :: Name -> PolyArgMap -> PolyArgMap
insertTV tv pam@(PolyArgMap pargm)
    | not $ member tv pam = PolyArgMap $ HM.insert tv [] pargm
    | otherwise = error "PolyArgMap.insertTV: inserting empty mapping for already existing tyVar"

insertRename :: Name -> Name -> Name -> Maybe Type -> PolyArgMap -> PolyArgMap
insertRename tv env ren ty (PolyArgMap pargm) | HM.member tv pargm =
    PolyArgMap $ HM.adjust (modifyPAMEntries env ren ty) tv pargm
  | otherwise = error ("PolyArgMap.insertRename: trying to insert into set of TyVar not in map: " ++ show tv)
  where modifyPAMEntries :: Name -> Name -> Maybe Type -> [PAMEntry] -> [PAMEntry]
        modifyPAMEntries e r mt pes = case find (\pe -> envN pe == e) pes of
            Just pe -> map (\pEnt -> if pEnt == pe then pEnt {runN=r} else pEnt) pes
            Nothing -> (PAMEntry {envN=e, runN=r, vOrF=maybe Val Func mt}):pes

lookup :: Name -> PolyArgMap -> Maybe [(Name, Name, Maybe Type)]
lookup tv (PolyArgMap pargm) = case HM.lookup tv pargm of
                    Just entries -> Just (map (\ent -> (envN ent, runN ent, (\case Val -> Nothing; Func t -> Just t) (vOrF ent))) entries)
                    Nothing -> Nothing

member :: Name -> PolyArgMap -> Bool
member n pam = isJust (lookup n pam)

remove :: Name -> PolyArgMap -> PolyArgMap
remove i (PolyArgMap pargm) = let pargm' = HM.delete i pargm in
            if pargm == pargm'
            then error "PolyArgMap.remove: removing nonexistent TV"
            else PolyArgMap pargm'

toList :: PolyArgMap -> [(Name, [(Name, Name, Maybe Type)])]
toList (PolyArgMap pargm) = map (second (map makeEntryTuple)) (HM.toList pargm)
    where makeEntryTuple :: PAMEntry -> (Name, Name, Maybe Type)
          makeEntryTuple (PAMEntry e r vorf) = (e, r, (\case Val -> Nothing; Func t -> Just t) vorf)

fromList :: [(Name, [(Name, Name, Maybe Type)])] -> PolyArgMap
fromList l = PolyArgMap $ HM.fromList (map (second (map fromEntryTuple)) l)
    where fromEntryTuple :: (Name, Name, Maybe Type) -> PAMEntry
          fromEntryTuple (e, r, mt) = PAMEntry {envN=e, runN=r, vOrF=maybe Val Func mt}

empty :: PolyArgMap
empty = PolyArgMap HM.empty

instance Hashable ValOrFunc
instance Hashable PAMEntry
instance Hashable PolyArgMap
