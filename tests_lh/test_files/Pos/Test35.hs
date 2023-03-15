{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}
 
{-# LANGUAGE DeriveGeneric #-}

module Combined ( List
                , kmeans1) where

import Prelude hiding (length, replicate, foldr, foldr1, map, concat, zipWith, repeat)

import Data.List (minimumBy)

{-@ die :: {v:String | false} -> a @-}
die str = error ("Oops, I died!" ++ str)

data List a = Emp
            | C a
              deriving (Eq, Ord, Show)

{-@ measure size      :: List a -> Int
        size (Emp)        = 0
    size (C x) = 1
  @-}

{-@ invariant {v:List a | 0 <= size v} @-}
{-@ invariant {v:List a | size v <= 1} @-}

{-@ type ListN a N  = {v:List a | size v = N} @-}

{-@ zipWith ::xs:List Double -> {ys:List Double | size xs == size ys} -> Double @-}
zipWith   :: List Double -> List Double -> Double
zipWith Emp Emp               = 0
zipWith (C x) (C y) = x
zipWith _          _          = die  "Bad call to zipWith"

map :: (a -> (k, v)) -> List a -> List (k, v)
map f Emp        = Emp
map f (C x) = C (f x)

-- | N-Dimensional Point
type Point   = List Double

{-@ type PointN N = ListN Double N @-}

distance :: Point -> Point -> Double
distance px py = zipWith px py

nearest   :: [(Int, Point)] -> Point -> Int
nearest centers p = minKeyFuncList centers f
  where
    f x1 x2 = compare (distance (snd x1) p) (distance (snd x2) p)

minKeyFuncList :: [(k,v)] -> ((k,v) -> (k,v) -> Ordering) -> k
minKeyFuncList xs f = fst $ minimumBy f xs

{-@ kmeans1 :: List (PointN 1) -> [(Int, (PointN 1))] -> List (Int, Point) @-}
kmeans1   :: List Point -> [(Int, Point)] -> List (Int, Point)
kmeans1 ps cs = map fm ps
  where
    fm p          = (nearest cs p, p)
