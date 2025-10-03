{-# LANGUAGE DeriveDataTypeable, DeriveGeneric, LambdaCase #-}

module G2.Language.PolyArgMap ( PolyArgMap
                               , insertTV
                               , insertRToE
                               , insertRename
                               , lookup
                               , lookupInRToE
                               , lookupInBoth
                               , member
                               , memberTV
                               , toLists
                               , fromLists
                               , rToEHashMap
                               , empty ) where

import G2.Language.Syntax

import qualified Data.HashMap.Lazy as HM
import Data.Data (Data, Typeable)
import Data.Hashable(Hashable)
import Data.List (find)
import Data.Bifunctor (second)
import GHC.Generics (Generic)
import Prelude hiding (lookup)
import Data.Maybe (isJust, fromJust)

-- | Interface for the PAM

-- If the name is a val of the TV type, we already know it's type.
data ValOrFunc = Val | Func Type deriving (Show, Eq, Read, Data, Typeable, Generic)
data PAMEntry = PAMEntry {envN :: Name, runN :: Name, vOrF :: ValOrFunc} deriving (Show, Eq, Read, Data, Typeable, Generic)
data PolyArgMap = PolyArgMap {arg_map :: HM.HashMap Name [PAMEntry], run_to_env :: HM.HashMap Name Name} deriving (Show, Eq, Read, Data, Typeable, Generic)

insertTV :: Name -> PolyArgMap -> PolyArgMap
insertTV tv pam = pam {arg_map = HM.insert tv [] $ arg_map pam}

insertRToE :: Name -> Name -> PolyArgMap -> PolyArgMap 
insertRToE r e pam = pam {run_to_env = HM.insert r e $ run_to_env pam}

-- TODO: make this better
-- | Insert a new runtime->environment argument mapping for the envTV that runTV maps to.
insertRename :: Name -> Name -> Name -> Maybe Type -> PolyArgMap -> PolyArgMap 
insertRename runTV eArg rArg mty pam | member runTV pam = 
      pam {arg_map = HM.adjust (modifyPAMEntries eArg rArg mty) (fromJust . HM.lookup runTV $ run_to_env pam) (arg_map pam)} 
    -- TODO: should this still error
    | otherwise = error ("PolyArgMap.insertRename: trying to insert into set of TyVar not in map: " ++ show runTV)
        where modifyPAMEntries :: Name -> Name -> Maybe Type -> [PAMEntry] -> [PAMEntry]
              modifyPAMEntries e r mt pes = case find (\pe -> envN pe == e) pes of
                        Just pe -> map (\pEnt -> if pEnt == pe then pEnt {runN=r} else pEnt) pes
                        Nothing -> (PAMEntry {envN=e, runN=r, vOrF=maybe Val Func mt}):pes

-- | Lookup the entries for an runtime TV using run_to_env.
lookup :: Name -> PolyArgMap -> Maybe [(Name, Name, Maybe Type)]
lookup runTV pam = HM.lookup runTV (run_to_env pam) >>= flip HM.lookup (arg_map pam) >>= (Just . map makeEntryTuple)

lookupInRToE :: Name -> PolyArgMap -> Maybe Name
lookupInRToE tv pam = HM.lookup tv (run_to_env pam)

lookupInBoth :: Name -> PolyArgMap -> Maybe [(Name, Name, Maybe Type)]
lookupInBoth tv pam = case lookup tv pam of 
                            Just ents -> Just ents
                            Nothing -> case HM.lookup tv (arg_map pam) of
                                Just ents -> Just (map makeEntryTuple ents)
                                Nothing -> Nothing

-- | Check if a runtime TV is present in the PolyArgMap.
member :: Name -> PolyArgMap -> Bool
member n pam = isJust (lookup n pam)

-- | Check directly if an environment TV is mapped in the PolyArgMap. 
memberTV :: Name -> PolyArgMap -> Bool 
memberTV env pam = HM.member env $ arg_map pam

toLists :: PolyArgMap -> ([(Name, [(Name, Name, Maybe Type)])], [(Name, Name)])
toLists pam = (map (second (map makeEntryTuple)) (HM.toList $ arg_map pam), HM.toList $ run_to_env pam)

fromLists :: ([(Name, [(Name, Name, Maybe Type)])], [(Name, Name)]) -> PolyArgMap
fromLists (am, rte) = PolyArgMap { arg_map = HM.fromList (map (second (map fromEntryTuple)) am), 
                                  run_to_env = HM.fromList rte } 
    where fromEntryTuple :: (Name, Name, Maybe Type) -> PAMEntry
          fromEntryTuple (e, r, mt) = PAMEntry {envN=e, runN=r, vOrF=maybe Val Func mt}
          
makeEntryTuple :: PAMEntry -> (Name, Name, Maybe Type)
makeEntryTuple (PAMEntry e r vorf) = (e, r, (\case Val -> Nothing; Func t -> Just t) vorf)

-- TODO: should we just access the field in Rules.hs?
rToEHashMap :: PolyArgMap -> HM.HashMap Name Name
rToEHashMap = run_to_env

empty :: PolyArgMap
empty = PolyArgMap HM.empty HM.empty        

instance Hashable ValOrFunc
instance Hashable PAMEntry
instance Hashable PolyArgMap
