module UFMapTests where

import G2.Data.UFMap

import Data.Hashable
import qualified Data.List as L
import Data.Maybe as M

import Test.Tasty
import Test.Tasty.QuickCheck

import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as S

import Prelude hiding (lookup, map, null)
import qualified Prelude as P

ufMapQuickcheck :: TestTree
ufMapQuickcheck =
    testGroup "UFMap" [
          testProperty "from hashset to hashset" prop_from_hs_to_hs
        , testProperty "insert forces in list" prop_insert_forces_in_list
        , testProperty "after joining two keys, they will return the same result from lookup" join_makes_lookup_match
        , testProperty "lookup j after joining nonpresent j with some k in the map" prop_lookup_after_joining
        , testProperty "if two keys are joined in the first map, they are joined after merging that map" prop_merge_preserves_joins1
        , testProperty "if two keys are joined in the second map, they are joined after merging that map" prop_merge_preserves_joins2
        , testProperty "if a key is present in two maps being merged, in will be present in the merge" prop_merge_preserves_values
        , testProperty "if a key is present in two maps being merged, in will be present in the merge (less thorough, but simpler)" prop_merge_preserves_values_simple
        , testProperty "merge function is applied to all values from original map" prop_merge_merges_values
        , testProperty "toList . fromList preserves joins" prop_toList_fromList_joins
        , testProperty "toList . fromList preserves stored values" prop_toList_fromList_values
        , testProperty "the toList function returns a list with at least as many elements as in the simple map" prop_toList_leq_simple_map

        , testProperty "the unionWith function correctly preserves elements in the first UFMaps" prop_unionWith_preserves_values1
        , testProperty "the unionWith function correctly preserves elements in the second UFMaps" prop_unionWith_preserves_values2
        ]

prop_from_hs_to_hs :: [([Integer], Maybe Integer)] -> Property
prop_from_hs_to_hs xs =
    let
        xs_tails = L.init $ L.tails xs
        xs' = [ (ks', v) | ((ks, v):xs_tls') <- xs_tails
                         , let later_ks = concat (P.map fst xs_tls')
                         , let ks' = P.filter (\k -> k `notElem` later_ks) ks ]
        hs = toHS xs'
    in
    all (not . P.null . fst) xs'
    ==>
    property (hs == toSet (fromSet hs))

toHS :: (Hashable k, Eq k, Hashable v, Eq v) => [([k], Maybe v)] -> S.HashSet (S.HashSet k, Maybe v)
toHS = S.fromList . mapMaybe (\(ks, v) -> if isJust v
                                                then Just (S.fromList ks, v)
                                                else Nothing )

prop_insert_forces_in_list :: Integer -> Integer -> UFMap Integer Integer -> Property
prop_insert_forces_in_list k v ufm =
    let
        ufm' = insert k v ufm
        lst = toList ufm'
    in
    property (any (\(ks, v') -> k `elem` ks
                            && case v' of
                                    Just v'' -> v == v''
                                    Nothing -> False) lst)

join_makes_lookup_match :: Fun (Integer, Integer) Integer -> Integer -> Integer -> UFMap Integer Integer -> Property
join_makes_lookup_match (Fn2 f) x y ufm =
    let
        ufm' = join f x y ufm
    in
    property (lookup x ufm' == lookup y ufm')

prop_lookup_after_joining :: Integer -> UFMap Integer Integer -> Property
prop_lookup_after_joining j ufm =
    let
        ks = keys ufm
        k = head ks
    in
    not (L.null ks) && j `notElem` ks
    ==>
    property $ lookup j (join undefined j k ufm) == lookup k ufm

prop_merge_preserves_joins1 :: Integer
                            -> Integer
                            -> Fun (Integer, Integer) Integer
                            -> Fun (Integer, Integer, Integer) (Integer, [(Integer, Integer)])
                            -> Fun (Integer, Integer) (Integer, [(Integer, Integer)])
                            -> Fun (Integer, Integer) (Integer, [(Integer, Integer)])
                            -> Fun (Integer, Integer) Integer
                            -> Fun (Integer, Integer) Integer
                            -> Fun (Integer, Integer) Integer
                            -> UFMap Integer Integer
                            -> UFMap Integer Integer
                            -> Property
prop_merge_preserves_joins1 x y (Fn2 jf) (Fn3 fb) (Fn2 f1) (Fn2 f2) (Fn2 fj1) (Fn2 fj2) (Fn2 j) ufm1 ufm2 =
    let
        ufm1' = join jf x y ufm1
    
        m_ufm = mergeJoiningWithKey fb f1 f2 fj1 fj2 j ufm1' ufm2
    in
    property (lookup x m_ufm == lookup y m_ufm)

prop_merge_preserves_joins2 :: Integer
                            -> Integer
                            -> Fun (Integer, Integer) Integer
                            -> Fun (Integer, Integer, Integer) (Integer, [(Integer, Integer)])
                            -> Fun (Integer, Integer) (Integer, [(Integer, Integer)])
                            -> Fun (Integer, Integer) (Integer, [(Integer, Integer)])
                            -> Fun (Integer, Integer) Integer
                            -> Fun (Integer, Integer) Integer
                            -> Fun (Integer, Integer) Integer
                            -> UFMap Integer Integer
                            -> UFMap Integer Integer
                            -> Property
prop_merge_preserves_joins2 x y (Fn2 jf) (Fn3 fb) (Fn2 f1) (Fn2 f2) (Fn2 fj1) (Fn2 fj2) (Fn2 j) ufm1 ufm2 =
    let
        ufm2' = join jf x y ufm2
    
        m_ufm = mergeJoiningWithKey fb f1 f2 fj1 fj2 j ufm1 ufm2'
    in
    property (lookup x m_ufm == lookup y m_ufm)

prop_merge_preserves_values :: Integer
                            -> Fun (Integer, Integer, Integer) (Integer, [(Integer, Integer)])
                            -> Fun (Integer, Integer) (Integer, [(Integer, Integer)])
                            -> Fun (Integer, Integer) (Integer, [(Integer, Integer)])
                            -> Fun (Integer, Integer) Integer
                            -> Fun (Integer, Integer) Integer
                            -> Fun (Integer, Integer) Integer
                            -> UFMap Integer Integer
                            -> UFMap Integer Integer
                            -> Property
prop_merge_preserves_values x (Fn3 fb) (Fn2 f1) (Fn2 f2) (Fn2 fj1) (Fn2 fj2) (Fn2 j) ufm1 ufm2 =
    let
        m_ufm = mergeJoiningWithKey fb f1 f2 fj1 fj2 j ufm1 ufm2
    in
    isJust (lookup x ufm1) || isJust (lookup x ufm2)
    ==>
    property (isJust (lookup x m_ufm))

prop_merge_preserves_values_simple :: Integer
                                   -> Fun (Integer, Integer) (Integer, [(Integer, Integer)])
                                   -> UFMap Integer Integer
                                   -> UFMap Integer Integer
                                   -> Property
prop_merge_preserves_values_simple x (Fn2 f2) ufm1 ufm2 =
    let
        m_ufm = mergeJoiningWithKey (\_ x y -> (x + y, [])) (\_ x -> (x, [])) f2 (+) (+) (+) ufm1 ufm2
    in
    isJust (lookup x ufm1) || isJust (lookup x ufm2)
    ==>
    property (isJust (lookup x m_ufm))

prop_merge_merges_values :: Integer
                         -> UFMap Integer (S.HashSet Integer)
                         -> UFMap Integer (S.HashSet Integer)
                         -> Property
prop_merge_merges_values x ufm1 ufm2 = 
    let
        m_ufm = mergeJoiningWithKey (\_ x y -> (S.union x y, []))
                                    (\_ x -> (x, []))
                                    (\_ x -> (x, []))
                                    S.union
                                    S.union
                                    S.union
                                    ufm1 ufm2
        s1 = case lookup x ufm1 of
                    Just s -> s
                    Nothing -> S.empty 
        s2 = case lookup x ufm2 of
                    Just s -> s
                    Nothing -> S.empty
    in
    not (S.null s1) || not (S.null s2)
    ==>
    property (s1 `isSubsetOf` (m_ufm ! x) && s2 `isSubsetOf` (m_ufm ! x))

isSubsetOf :: (Eq a, Hashable a) => S.HashSet a -> S.HashSet a -> Bool
isSubsetOf xs ys = all (\x -> x `S.member` ys) $ S.toList xs

prop_toList_fromList_joins :: Integer
                           -> Integer
                           -> UFMap Integer (S.HashSet Integer)
                           -> Property
prop_toList_fromList_joins i1 i2 ufm =
    let
        ufm' = fromList . toList $ join S.union i1 i2 ufm
    in
    property $ lookupRep i1 ufm' == lookupRep i2 ufm'

prop_toList_fromList_values :: Integer
                            -> S.HashSet Integer
                            -> UFMap Integer (S.HashSet Integer)
                            -> Property
prop_toList_fromList_values i hs ufm =
    let
        ufm' = fromList . toList $ insert i hs ufm
    in
    property $ lookup i ufm' == Just hs

prop_toList_leq_simple_map :: [(Integer, S.HashSet Integer)] -> UFMap Integer (S.HashSet Integer) -> Property
prop_toList_leq_simple_map els ufm =
    let
        ufm' = foldr (uncurry insert) ufm els
    in
    property $ length (toList ufm') >= HM.size (toSimpleMap ufm')

prop_unionWith_preserves_values1 :: Integer
                                  -> UFMap Integer (S.HashSet Integer)
                                  -> UFMap Integer (S.HashSet Integer)
                                  -> Property
prop_unionWith_preserves_values1 x ufm1 ufm2 =
    let
        union = unionWith HS.union ufm1 ufm2

        s1 = case lookup x ufm1 of
                    Just s -> s
                    Nothing -> S.empty 
        s2 = case lookup x union of
                    Just s -> s
                    Nothing -> S.empty
    in
    not (S.null s1) || not (S.null s2) ==> property $ s1 `isSubsetOf` s2

prop_unionWith_preserves_values2 :: Integer
                                 -> UFMap Integer (S.HashSet Integer)
                                 -> UFMap Integer (S.HashSet Integer)
                                 -> Property
prop_unionWith_preserves_values2 x ufm1 ufm2 =
    let
        union = unionWith HS.union ufm1 ufm2

        s1 = case lookup x ufm2 of
                    Just s -> s
                    Nothing -> S.empty 
        s2 = case lookup x union of
                    Just s -> s
                    Nothing -> S.empty
    in
    not (S.null s1) || not (S.null s2) ==> property $ s1 `isSubsetOf` s2

instance (Hashable a, Eq a, Arbitrary a) => Arbitrary (S.HashSet a) where
    arbitrary = return . S.fromList =<< arbitrary
    shrink = P.map S.fromList . shrink . S.toList
