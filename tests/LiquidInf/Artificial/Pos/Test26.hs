{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

module ListQualif ( List ) where

import Prelude hiding (foldr, foldr1, map)
import Data.List (minimumBy)
import qualified Data.Map as M

infixr 9 :+:

{-@ die :: {v:String | false} -> a @-}
die str = error ("Oops, I died!" ++ str)

{-@ type TRUE = {v:Bool | v} @-}
{-@ lAssert :: TRUE -> TRUE @-}
lAssert True  = True
lAssert False = die "Assert Fails!"

data List a = Emp
            | (:+:) a (List a)
              deriving (Eq, Ord, Show)

{-@ measure size      :: List a -> Int
    size (Emp)        = 0
    size ((:+:) x xs) = 1 + size xs @-}

{-@ invariant {v:List a | 0 <= size v} @-}

map       :: (a -> b) -> List a -> List b
map f Emp        = Emp
map f (x :+: xs) = f x :+: map f xs

foldr1 op (x :+: xs) = foldr op x xs
foldr1 op Emp        = die "Cannot call foldr1 with empty list"

foldr :: (a -> b -> b) -> b -> List a -> b
foldr _  b Emp        = b
foldr op b (x :+: xs) = x `op` foldr op b xs

mapReduce :: (Ord k) => (a -> (k, v)) -> List a -> M.Map k v
mapReduce fm xs = kvsm
  where
    kvs   = map fm xs
    kvsm  = foldr addKV  M.empty  kvs

addKV (k,v) m = M.insert k v m

divide :: Double -> Int -> Double
divide n 0 = die "oops divide by zero"
divide n d = n / (fromIntegral d)

type Point   = List Double
{-@ type PointN N = {v:List Double | size v = N} @-}

{-@ type IntK K = {v:Int | 0 <= v && v < K} @-}

type Centering = M.Map Int Point
{-@ type CenteringKN K N = M.Map (IntK K) (PointN N) @-}

{-@ nearest :: k:Nat -> n:Nat -> CenteringKN k n -> PointN n -> IntK k @-}
nearest   :: Int -> Int -> Centering -> Point -> Int
nearest k n centers p = minKeyFuncList (M.toList centers)

minKeyFuncList :: (Ord v) => [(k,v)] -> k
minKeyFuncList xs = fst $ minimumBy (\_ _ -> EQ) xs

centroid :: Int -> Point -> Int -> Point
centroid n p sz = map (\x -> x `divide` sz) p

{-@ kmeans1 :: k:Nat -> n:Nat ->
               List (PointN n) -> CenteringKN k n -> CenteringKN k n @-}
kmeans1   :: Int -> Int -> List Point -> Centering -> Centering
kmeans1 k n ps cs = normalize newClusters
  where
    normalize     :: M.Map a (Int, Point) -> M.Map a Point
    normalize     = M.map (\(sz, p) -> centroid n p sz)
    newClusters   = mapReduce fm ps
    fm p          = (nearest k n cs p, (1 :: Int, p))
