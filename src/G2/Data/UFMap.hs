{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TupleSections #-}

module G2.Data.UFMap ( UFMap
                     , empty
                     , toList
                     , fromList
                     , toSet
                     , fromSet
                     , toSimpleMap
                     , join
                     , joinAll
                     , lookup
                     , lookupWithRep
                     , lookupRep
                     , (!)
                     , find
                     , insert
                     , insertWith
                     , adjust
                     , alter
                     , clear
                     , filterWithKey

                     , unionWith
                     , mergeJoiningWithKey

                     , map

                     , null
                     , keys
                     , joinedKeys
                     , elems
                     , member) where

import qualified G2.Data.UnionFind as UF

import Control.Exception
import qualified Control.Monad as Mon

import Data.Data (Data (..), Typeable)
import Data.Hashable
import qualified Data.HashMap.Lazy as M
import qualified Data.HashSet as S
import qualified Data.List as L
import Data.Maybe

import Prelude hiding (lookup, null, map)
import qualified Prelude as P

import Text.Read
import qualified Text.Read.Lex as L
import GHC.Read

import GHC.Generics (Generic)

import Test.Tasty.QuickCheck

data UFMap k v = UFMap { joined :: UF.UnionFind k
                       , store :: M.HashMap k v }
                       deriving (Typeable, Data, Generic)

instance (Eq k, Hashable k, Hashable v) => Hashable (UFMap k v)

empty :: UFMap k v
empty = UFMap UF.empty M.empty

toList :: (Eq k, Hashable k) => UFMap k v -> [([k], Maybe v)]
toList uf =
    let
        uf_l = UF.toList $ joined uf

        c_uf_l = concat uf_l
        not_acc = P.map (:[]) $ keys uf L.\\ c_uf_l
    in
    P.map (\l -> (l, lookup (head l) uf)) $ uf_l ++ not_acc

toSet :: (Eq k, Eq v, Hashable k, Hashable v) => UFMap k v -> S.HashSet (S.HashSet k, Maybe v)
toSet = S.fromList . P.map (\(ks, v) -> (S.fromList ks, v)) . toList

fromList :: (Eq k, Hashable k) => [([k], Maybe v)] -> UFMap k v
fromList xs =
    let
        xs_j = concatMap (\(ks, v) -> case v of 
                                            Just v' -> P.map (\k -> (k, v')) ks
                                            Nothing -> [] ) xs
        m = foldr (uncurry insert) empty xs_j
    in
    foldr (\(ks, _) m' ->
                case ks of
                    [] -> m'
                    (k:_) -> foldr (\k' -> join const k k') m' ks)
          m xs

fromSet :: (Eq k, Hashable k) => S.HashSet (S.HashSet k, Maybe v) -> UFMap k v
fromSet = fromList . P.map (\(ks, v) -> (S.toList ks, v)) . S.toList

toSimpleMap :: UFMap k v -> M.HashMap k v
toSimpleMap = store

-- | Joins two keys, regardless of whether they are present in the map.
-- If the keys are already joined, the map is not changed
join :: (Eq k, Hashable k) => (v -> v -> v) -> k -> k -> UFMap k v -> UFMap k v
join f k1 k2 ufm@(UFMap uf m)
    | UF.find k1 uf == UF.find k2 uf = ufm
    | otherwise =
        let
            (r1, v1) = lookupWithRep k1 ufm
            (r2, v2) = lookupWithRep k2 ufm

            uf' = UF.union k1 k2 uf
            r = UF.find k1 uf'

            m' = M.delete r1 . M.delete r2 $ m

            m'' = case (v1, v2) of
                    (Just v1', Just v2') -> M.insert r (f v1' v2') m'
                    (Just v1', _) -> M.insert r v1' m'
                    (_, Just v2') -> M.insert r v2' m'
                    _ -> m
        in
        assert (isNothing (M.lookup k1 m'') || isNothing (M.lookup k2 m''))
            UFMap uf' m''

joinAll :: (Eq k, Hashable k) => (v -> v -> v) -> [k] -> UFMap k v -> UFMap k v
joinAll _ [] uf = uf
joinAll f xs@(x:_) uf = foldr (join f x) uf xs

lookup :: (Eq k, Hashable k) => k -> UFMap k v -> Maybe v
lookup k = snd . lookupWithRep k

lookupWithRep :: (Eq k, Hashable k) => k -> UFMap k v -> (k, Maybe v)
lookupWithRep k (UFMap uf m) =
    let r = UF.find k uf in
    (r, M.lookup r m)

lookupRep :: (Eq k, Hashable k) => k -> UFMap k v -> k
lookupRep k (UFMap uf _) = UF.find k uf

(!) :: (Eq k, Hashable k) => UFMap k v -> k -> v
uf ! k = case lookup k uf of
                Just v -> v
                Nothing -> error "!: key not found"

find :: (Eq k, Hashable k) => k -> UFMap k v -> k
find k = UF.find k . joined

insert :: (Eq k, Hashable k) => k -> v -> UFMap k v -> UFMap k v
insert k v (UFMap uf m) =
    let
        m' = M.insert (UF.find k uf) v m
    in
    assert (UF.find k uf == k || isNothing (M.lookup k m'))
        UFMap uf m'

insertWith :: (Eq k, Hashable k) => (v -> v -> v) -> k -> v -> UFMap k v -> UFMap k v
insertWith f k v (UFMap uf m) = UFMap uf $ M.insertWith f (UF.find k uf) v m

adjust :: (Eq k, Hashable k) => (v -> v) -> k -> UFMap k v -> UFMap k v
adjust f k (UFMap uf m) = UFMap uf $ M.adjust f (UF.find k uf) m

alter :: (Eq k, Hashable k) => (Maybe v -> Maybe v) -> k -> UFMap k v -> UFMap k v
alter f k (UFMap uf m) = UFMap uf $ M.alter f (UF.find k uf) m

-- | Preserves the joined keys, but deletes all contained elements
clear :: UFMap k v -> UFMap k v
clear (UFMap uf _) = UFMap uf M.empty

filterWithKey :: (k -> v -> Bool) -> UFMap k v -> UFMap k v
filterWithKey p (UFMap uf m) = UFMap uf $ M.filterWithKey p m

unionWith :: (Eq k, Hashable k) => (v -> v -> v) -> UFMap k v -> UFMap k v -> UFMap k v
unionWith f ufm1 (UFMap uf2 m2) =
    let
        ufm1' = foldr (joinAll f) ufm1 (UF.toList uf2) 
    in
    M.foldrWithKey (insertWith f) ufm1' m2 

-- One key (from the joined set of keys) is given
mergeJoiningWithKey :: (Eq k, Hashable k, Show k, Show v, Show v1, Show v2)
                    => (k -> v1 -> v2 -> (v, [(k, k)])) -- ^ How to merge values that are joined from both maps
                    -> (k -> v1 -> (v, [(k, k)])) -- ^ How to merge values of keys only in the first map
                    -> (k -> v2 -> (v, [(k, k)])) -- ^ How to merge values of keys only in the second map
                    -> (v1 -> v1 -> v1) -- ^ How to merge values that are joined within the first map
                    -> (v2 -> v2 -> v2) -- ^ How to merge values that are joined within the second map
                    -> (v -> v -> v) -- ^ Final extra joins, generated by prior higher order functions
                    -> UFMap k v1
                    -> UFMap k v2
                    -> UFMap k v
mergeJoiningWithKey fb f1 f2 fj1 fj2 j (UFMap uf1 m1) (UFMap uf2 m2) =
    let
        j_uf = UF.unionOfUFs uf1 uf2

        -- We build a map where the keys are the values of j_f, and the values have type (Maybe v1, Maybe v2)
        j_m1 = foldr (\(k, v) m ->
                            let uf_k = UF.find k j_uf in
                            case M.lookup uf_k m of
                                Nothing -> M.insert uf_k (Just v, Nothing) m
                                Just (Nothing, _) -> M.insert uf_k (Just v, Nothing) m
                                Just (Just v1, v2) -> M.insert uf_k (Just $ fj1 v v1, v2) m
                     ) M.empty (M.toList m1)
        j_m2 = foldr (\(k, v) m ->
                            let uf_k = UF.find k j_uf in
                            case M.lookup uf_k m of
                                Nothing -> M.insert uf_k (Nothing, Just v) m
                                Just (v1, Nothing) -> M.insert uf_k (v1, Just v) m
                                Just (v1, Just v2) -> M.insert uf_k (v1, Just $ fj2 v v2) m
                     ) j_m1 (M.toList m2)

        j_m = M.mapWithKey (\k (v1, v2) -> case (v1, v2) of
                                            (Just v1', Just v2') -> fb k v1' v2'
                                            (Just v1', Nothing) -> f1 k v1'
                                            (Nothing, Just v2') -> f2 k v2'
                                            _ -> error "merge: impossible state!") j_m2

        ks = concat . M.elems $ M.map snd j_m

        n_ufm = UFMap j_uf $ M.map fst j_m
        n_ufm' = foldr (uncurry (join j)) n_ufm ks
    in
    n_ufm'

map :: (v1 -> v2) -> UFMap k v1 -> UFMap k v2
map f uf = uf { store = M.map f $ store uf }

null :: UFMap k v -> Bool
null = M.null . store

keys :: (Eq k, Hashable k) => UFMap k v -> [k]
keys = S.toList . keysSet

keysSet :: (Eq k, Hashable k) => UFMap k v -> S.HashSet k
keysSet uf =
    (foldr S.union S.empty . UF.toSet . joined $ uf) `S.union` (M.keysSet . store $ uf)

joinedKeys :: UFMap k v -> UF.UnionFind k
joinedKeys = joined

elems :: UFMap k v -> [v]
elems = M.elems . store

member :: (Eq k, Hashable k) => k -> UFMap k v -> Bool
member k = M.member k . store

instance (Eq k, Eq v, Hashable k, Hashable v) => Eq (UFMap k v) where
    x == y = toSet x == toSet y

instance (Eq k, Hashable k, Show k, Show v) => Show (UFMap k v) where
    show uf = "fromList " ++ show (toList uf)


instance (Eq k, Hashable k, Read k, Read v) => Read (UFMap k v) where
    readPrec = parens $
                    do expectP (L.Ident "fromList")
                       x <- step readListPrec
                       return (fromList x)
    readListPrec = readListPrecDefault 

instance (Arbitrary k, Arbitrary v, Eq k, Hashable k) => Arbitrary (UFMap k v) where
    arbitrary = do       
        ufsz <- arbitrary
        jnum <- arbitrary
        ks <- Mon.replicateM ufsz arbitrary
        vs <- Mon.replicateM ufsz arbitrary
        js <- Mon.replicateM jnum arbitrary

        let uf = foldr (uncurry insert) empty (zip ks vs)
            ufm = foldr (uncurry (join const)) uf js

        return ufm

    shrink = P.map fromList . shrink . toList
    -- shrink = P.map (fromList . filter (not . P.null . fst)) . shrink . toList
