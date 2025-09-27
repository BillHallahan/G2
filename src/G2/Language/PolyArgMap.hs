{-# LANGUAGE DeriveDataTypeable, DeriveGeneric, LambdaCase #-}

module G2.Language.PolyArgMap ( PolyArgMap
                               , insertTV
                               , insertRename
                               , lookup
                               , member
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
data PolyArgMap = PolyArgMap {poly_arg_map :: HM.HashMap Name [PAMEntry], run_to_env :: HM.HashMap Name Name} deriving (Show, Eq, Read, Data, Typeable, Generic)

insertTV :: Name -> PolyArgMap -> PolyArgMap
insertTV tv pam = pam {poly_arg_map = HM.insert tv [] $ poly_arg_map pam}

insertRename :: Name -> Name -> Name -> Maybe Type -> PolyArgMap -> PolyArgMap
insertRename tv env ren ty pam | HM.member tv (poly_arg_map pam) =
    pam {poly_arg_map = HM.adjust (modifyPAMEntries env ren ty) tv (poly_arg_map pam)} 
  | otherwise = error ("PolyArgMap.insertRename: trying to insert into set of TyVar not in map: " ++ show tv)
  where modifyPAMEntries :: Name -> Name -> Maybe Type -> [PAMEntry] -> [PAMEntry]
        modifyPAMEntries e r mt pes = case find (\pe -> envN pe == e) pes of
            Just pe -> map (\pEnt -> if pEnt == pe then pEnt {runN=r} else pEnt) pes
            Nothing -> (PAMEntry {envN=e, runN=r, vOrF=maybe Val Func mt}):pes

lookup :: Name -> PolyArgMap -> Maybe [(Name, Name, Maybe Type)]
lookup tv pam = case HM.lookup tv (poly_arg_map pam) of
                    Just entries -> Just (map makeEntryTuple entries)
                    Nothing -> Nothing

member :: Name -> PolyArgMap -> Bool
member n pam = isJust (lookup n pam)

toList :: PolyArgMap -> [(Name, [(Name, Name, Maybe Type)])]
toList pam = map (second (map makeEntryTuple)) (HM.toList $ poly_arg_map pam)
             
makeEntryTuple :: PAMEntry -> (Name, Name, Maybe Type)
makeEntryTuple (PAMEntry e r vorf) = (e, r, (\case Val -> Nothing; Func t -> Just t) vorf)

fromList :: [(Name, [(Name, Name, Maybe Type)])] -> PolyArgMap
fromList l = PolyArgMap {poly_arg_map = HM.fromList (map (second (map fromEntryTuple)) l), run_to_env = HM.empty} 
    where fromEntryTuple :: (Name, Name, Maybe Type) -> PAMEntry
          fromEntryTuple (e, r, mt) = PAMEntry {envN=e, runN=r, vOrF=maybe Val Func mt}

empty :: PolyArgMap
empty = PolyArgMap HM.empty HM.empty

instance Hashable ValOrFunc
instance Hashable PAMEntry
instance Hashable PolyArgMap
