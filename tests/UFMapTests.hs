module UFMapTests where

import G2.Data.UFMap

import Data.Hashable
import qualified Data.List as L
import Data.Maybe as M

import Test.Tasty
import Test.Tasty.QuickCheck

import qualified Data.HashSet as S
import Data.Maybe

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
