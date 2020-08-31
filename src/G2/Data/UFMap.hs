{-# LANGUAGE DeriveDataTypeable #-}

module G2.Data.UFMap ( UFMap
                     , empty
                     , toList
                     , fromList
                     , join
                     , lookup
                     , insert
                     , adjust
                     , alter

                     , unionWith

                     , map

                     , null
                     , keys
                     , elems) where

import qualified G2.Data.UnionFind as UF

import Data.Data (Data (..), Typeable)
import Data.Hashable
import qualified Data.HashMap.Lazy as M
import qualified Data.List as L
import Data.Maybe

import Prelude hiding (lookup, null, map)
import qualified Prelude as P

import Text.Read
import qualified Text.Read.Lex as L
import GHC.Read

data UFMap k v = UFMap { joined :: UF.UnionFind k
                       , store :: M.HashMap k v }
                       deriving (Typeable, Data)

empty :: UFMap k v
empty = UFMap UF.empty M.empty

toList :: (Eq k, Hashable k) => UFMap k v -> [([k], v)]
toList uf =
    let
        uf_l = UF.toList $ joined uf

        c_uf_l = concat uf_l
        not_acc = P.map (:[]) $ keys uf L.\\ c_uf_l
    in
    P.map (\l -> (l, uf ! head l)) $ uf_l ++ not_acc

fromList :: (Eq k, Hashable k) => [([k], v)] -> UFMap k v
fromList xs =
    let
        xs_j = concatMap (\(ks, v) -> P.map (\k -> (k, v)) ks) xs
        m = foldr (uncurry insert) empty xs_j
    in
    foldr (\(ks, v) m' ->
                case ks of
                    [] -> m'
                    (k:_) -> foldr (\k' -> join k k' (\_ _ -> v)) m' ks)
          m xs

-- | Joins two keys, if at least one of them is present in the map.
join :: (Eq k, Hashable k) => k -> k -> (v -> v -> v) -> UFMap k v -> UFMap k v
join k1 k2 f ufm@(UFMap uf m) =
    let
        v1 = lookup k1 ufm
        v2 = lookup k2 ufm

        uf' = UF.union k1 k2 uf
        r = UF.find k1 uf'

        m' = M.delete k1 . M.delete k2 $ m
    in
    UFMap (if isJust v1 || isJust v2 then uf' else uf)
        $ case (v1, v2) of
            (Just v1', Just v2') -> M.insert r (f v1' v2') m'
            (Just v1', _) -> M.insert r v1' m'
            (_, Just v2') -> M.insert r v2' m'
            _ -> m

-- | Lifts find from the UnionFind
find :: (Eq k, Hashable k) => k -> UFMap k v -> k
find k = UF.find k . joined

lookup :: (Eq k, Hashable k) => k -> UFMap k v -> Maybe v
lookup k (UFMap uf m) = M.lookup (UF.find k uf) m

(!) :: (Eq k, Hashable k) => UFMap k v -> k -> v
UFMap uf m ! k = m M.! UF.find k uf

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

map :: (v1 -> v2) -> UFMap k v1 -> UFMap k v2
map f uf = uf { store = M.map f $ store uf }

null :: UFMap k v -> Bool
null = M.null . store

keys :: UFMap k v -> [k]
keys = M.keys . store

elems :: UFMap k v -> [v]
elems = M.elems . store

instance (Eq k, Hashable k, Show k, Show v) => Show (UFMap k v) where
    {-# NOINLINE show #-}
    show uf = "fromList " ++ show (toList uf) 


instance (Eq k, Hashable k, Read k, Read v) => Read (UFMap k v) where
    readPrec = parens $
                    do expectP (L.Ident "fromList")
                       x <- step readListPrec
                       return (fromList x)
    readListPrec = readListPrecDefault 
