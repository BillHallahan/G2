module UnionFindTests where

import G2.Data.UnionFind

import Data.Hashable
import qualified Data.List as L

import Test.Tasty
import Test.Tasty.QuickCheck

import qualified Data.HashSet as S

import Prelude hiding (lookup, map, null)
import qualified Prelude as P

unionFindQuickcheck :: TestTree
unionFindQuickcheck =
    testGroup "UnionFind" [
    	  testProperty "applyinf unionOfUfs preserves unions in the first UnionFind" prop_unionOfUFs_preserves_unions1
    	, testProperty "applyinf unionOfUfs preserves unions in the second UnionFind" prop_unionOfUFs_preserves_unions2
    	, testProperty "applyinf unionOfUfs creates new unions" prop_unionOfUFs_preserves_unions3
        ]

prop_unionOfUFs_preserves_unions1 :: Integer -> Integer -> UnionFind Integer -> UnionFind Integer -> Property
prop_unionOfUFs_preserves_unions1 x y uf1 uf2 =
	let
		uf1' = union x y uf1
		m_uf = unionOfUFs uf1' uf2
	in
	property (find x m_uf == find y m_uf)

prop_unionOfUFs_preserves_unions2 :: Integer -> Integer -> UnionFind Integer -> UnionFind Integer -> Property
prop_unionOfUFs_preserves_unions2 x y uf1 uf2 =
	let
		uf2' = union x y uf2
		m_uf = unionOfUFs uf1 uf2'
	in
	property (find x m_uf == find y m_uf)

prop_unionOfUFs_preserves_unions3 :: Integer -> Integer -> Integer -> UnionFind Integer -> UnionFind Integer -> Property
prop_unionOfUFs_preserves_unions3 x y z uf1 uf2 =
	let
		uf1' = union x y uf2
		uf2' = union y z uf2
		m_uf = unionOfUFs uf1' uf2'
	in
	property (find x m_uf == find z m_uf)