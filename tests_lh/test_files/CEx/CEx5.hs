{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}


{-# LANGUAGE DeriveGeneric #-}

module Combined ( List
                , kmeans1) where

import Prelude hiding (length, replicate, foldr, foldr1, map, concat, zipWith, repeat)

import qualified Data.Map as M

import Data.List (minimumBy)

infixr 9 :+:

empty     :: List a
add       :: a -> List a -> List a
singleton :: a -> List a
map       :: (a -> b) -> List a -> List b

{-@ type TRUE = {v:Bool | v} @-}

{-@ die :: {v:String | false} -> a @-}
die str = error ("Oops, I died!" ++ str)

{-@ lAssert :: TRUE -> TRUE @-}
lAssert True  = True
lAssert False = die "Assert Fails!"



data List a = Emp
            | (:+:) a (List a)
              deriving (Eq, Ord, Show)

{-@ measure size      :: List a -> Int
        size (Emp)        = 0
        size ((:+:) x xs) = 1 + size xs
  @-}

{-@ invariant {v:List a | 0 <= size v} @-}

{-@ type ListNE a = {v:List a | size v > 0} @-}

{-@ type ListN a N  = {v:List a | size v = N} @-}

{-@ type ListX a Xs = {v:List a | size v = size Xs} @-}

length            :: List a -> Int
length Emp        = 0
length (x :+: xs) = 1 + length xs

empty = Emp

add x xs = x :+: xs

singleton x = x :+: empty



map f Emp        = Emp
map f (x :+: xs) = f x :+: map f xs



centroid :: Int -> Point -> Int -> Point
kmeans1   :: Int -> Int -> List Point -> Centering -> Centering


divide :: Double -> Int -> Double
divide n 0 = die "oops divide by zero"
divide n d = n / (fromIntegral d)


-- | N-Dimensional Point
type Point   = List Double

{-@ type PointN N = ListN Double N @-}


type Center  = Int
{-@ type CenterK K = {v:Int | 0 <= v && v < K} @-}


type Centering = M.Map Center Point
{-@ type CenteringKN K N = M.Map (CenterK K) (PointN N) @-}


type Cluster = (Int, Point)

{-@ type ClusterN N = (Pos, PointN N) @-}
{-@ type Pos        = {v:Int | v > 0} @-}

{-@ centroid :: lq_tmp$x##9:GHC.Types.Int -> lq_tmp$x##10:(Combined.List GHC.Types.Double) -> lq_tmp$x##11:{lq_tmp$x##3 : GHC.Types.Int | (lq_tmp$x##3 > 0)} -> {lq_tmp$x##5 : (Combined.List GHC.Types.Double) | (size lq_tmp$x##5 == size lq_tmp$x##10)}  @-}
centroid n p sz = map (\x -> x `divide` sz) p

{-@ kmeans1 :: k:Nat -> n:Nat ->
              List (PointN n) -> CenteringKN k n -> CenteringKN k n
 @-}
kmeans1 k n ps cs = normalize newClusters
  where
    normalize     :: M.Map a Cluster -> M.Map a Point
    normalize     = M.map (\(sz, p) -> centroid n p sz)
    newClusters   = M.empty
    fm p          = singleton (1, (1 :: Int, p))
    fr wp1 wp2    = wp2
