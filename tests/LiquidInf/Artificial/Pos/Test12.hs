module Combined () where

import Prelude hiding (foldr, map, zipWith, repeat)

import qualified Data.Map as M

import Data.List (minimumBy)

data List a = Emp
            | D a
              deriving (Eq, Ord)

{-@ measure size :: List a -> Int
    size Emp = 0
    size (D x) = 1
  @-}

{-@ invariant {v:List a | 0 <= size v} @-}

{-@ type ListN a N  = {v:List a | size v = N} @-}

{-@ map :: (a -> b) -> xa : List a -> List b @-}
map :: (a -> b) -> List a -> List b
map f Emp = Emp
map f (D x) = D (f x)

foldr :: Ord k => List (k, v) -> M.Map k v
foldr Emp  = M.empty
foldr (D (k, v)) = M.insert k v M.empty

{-@ mapReduce :: (Ord k) => (Point -> (k, v)) -> List Point -> M.Map k v @-}
mapReduce :: (Ord k) => (Point -> (k, v)) -> List Point -> M.Map k v
mapReduce fm xs = foldr (map fm xs)

-- | N-Dimensional Point
type Point = List Int
{-@ type PointN N = ListN Int N @-}

{-@ nearest :: M.Map {v:Int | 0 <= v } Int -> Int @-}
nearest :: M.Map Int Int -> Int
nearest x = fst $ minimumBy (\_ _ -> LT) (M.toList x)

{-@ f :: k:Nat -> n:Nat -> List (PointN n) ->
         M.Map {v:Int | 0 <= v } Int -> M.Map {v:Int | 0 <= v } Int @-}
f :: Int -> Int -> List Point -> M.Map Int Int -> M.Map Int Int
f k n ps cs = M.map (\p -> p) newClusters
  where
    newClusters = mapReduce fm ps
    fm p = (nearest cs, 1)
