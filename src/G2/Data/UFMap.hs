{-# LANGUAGE DeriveDataTypeable #-}

module G2.Data.UFMap ( UFMap
                     , empty
                     , join
                     , lookup
                     , insert
                     , adjust
                     , alter

                     ,unionWith

                     , null
                     , keys
                     , elems
                     , toList) where

import qualified G2.Data.UnionFind as UF

import Data.Data (Data (..), Typeable)
import Data.Hashable
import qualified Data.HashMap.Lazy as M
import Prelude hiding (lookup, null)

data UFMap k v = UFMap { joined :: UF.UnionFind k
                       , store :: M.HashMap k v }
                       deriving (Show, Read, Typeable, Data)

empty :: UFMap k v
empty = UFMap UF.empty M.empty

join :: (Eq k, Hashable k) => k -> k -> (Maybe v -> Maybe v -> Maybe v) -> UFMap k v -> UFMap k v
join k1 k2 f ufm@(UFMap uf m) =
    let
        v1 = lookup k1 ufm
        v2 = lookup k2 ufm

        uf' = UF.union k1 k2 uf
        r = UF.find k1 uf'
    in
    UFMap uf' $ case f v1 v2 of
                    Just x -> M.insert r x m
                    Nothing -> M.delete r m

-- | Lifts find from the UnionFind
find :: (Eq k, Hashable k) => k -> UFMap k v -> k
find k = UF.find k . joined

lookup :: (Eq k, Hashable k) => k -> UFMap k v -> Maybe v
lookup k (UFMap uf m) = M.lookup (UF.find k uf) m

insert :: (Eq k, Hashable k) => k -> v -> UFMap k v -> UFMap k v
insert k v (UFMap uf m) = UFMap uf $ M.insert (UF.find k uf) v m

insertWith :: (Eq k, Hashable k) => (v -> v -> v) -> k -> v -> UFMap k v -> UFMap k v
insertWith f k v (UFMap uf m) = UFMap uf $ M.insertWith f (UF.find k uf) v m

adjust :: (Eq k, Hashable k) => (v -> v) -> k -> UFMap k v -> UFMap k v
adjust f k (UFMap uf m) = UFMap uf $ M.adjust f (UF.find k uf) m

alter :: (Eq k, Hashable k) => (Maybe v -> Maybe v) -> k -> UFMap k v -> UFMap k v
alter f k (UFMap uf m) = UFMap uf $ M.alter f (UF.find k uf) m

unionWith :: (Eq k, Hashable k) => (v -> v -> v) -> UFMap k v -> UFMap k v -> UFMap k v
unionWith f (UFMap uf1 m1) (UFMap uf2 m2) =
    let
        j_uf = UF.unionOfUFs uf1 uf2
        ufm1' = UFMap j_uf m1
    in
    M.foldrWithKey (insertWith f) ufm1' m2 

null :: UFMap k v -> Bool
null = M.null . store

keys :: UFMap k v -> [k]
keys = M.keys . store

elems :: UFMap k v -> [v]
elems = M.elems . store

toList :: UFMap k v -> [(k, v)]
toList = M.toList . store