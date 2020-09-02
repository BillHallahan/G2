module UFMapTests where

import G2.Data.UFMap

import Data.Hashable
import qualified Data.List as L

import Test.Tasty
import Test.Tasty.QuickCheck

import qualified Data.HashSet as S

import Prelude hiding (lookup, map, null)
import qualified Prelude as P

ufMapQuickcheck :: TestTree
ufMapQuickcheck =
    testGroup "UFMap" [
          testProperty "from hashset to hashset" prop_from_hs_to_hs
        , testProperty "insert forces in list" prop_insert_forces_in_list
        , testProperty "lookup j after joining nonpresent j with some k in the map" prop_lookup_after_joining
        ]

prop_from_hs_to_hs :: [([Integer], Integer)] -> Property
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


prop_insert_forces_in_list :: Integer -> Integer -> UFMap Integer Integer -> Property
prop_insert_forces_in_list k v ufm =
    let
        ufm' = insert k v ufm
        lst = toList ufm'
    in
    property (any (\(ks, v') -> k `elem` ks && v == v') lst)

prop_lookup_after_joining :: Integer -> UFMap Integer Integer -> Property
prop_lookup_after_joining j ufm =
    let
        ks = keys ufm
        k = head ks
    in
    not (L.null ks) && j `notElem` ks
    ==>
    property $ lookup j (join undefined j k ufm) == lookup k ufm

toHS :: (Hashable k, Eq k, Hashable v, Eq v) => [([k], v)] -> S.HashSet (S.HashSet k, v)
toHS = S.fromList . P.map (\(ks, v) -> (S.fromList ks, v))