\begin{code}
{-@ LIQUID "--short-names"    @-}
{-@ LIQUID "--no-termination" @-}

module KMeans (kmeans, kmeans1, nearest, mergeCluster) where

import Data.List (minimumBy)
import MapReduce
import List
import Prelude hiding (map, repeat, foldr, zipWith)
import qualified Data.Map as M

distance :: Int -> Point -> Point -> Double
nearest   :: Int -> Int -> Centering -> Point -> Center
mergeCluster :: Int -> Cluster -> Cluster -> Cluster
kmeans1   :: Int -> Int -> List Point -> Centering -> Centering
kmeans    :: Int -> Int -> Int -> List Point -> Centering -> Centering

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

{-@ distance :: n:Nat -> PointN n -> PointN n -> {d:Double | d > 0.1} @-}
distance n px py = sqrt $ foldr (+) 0 $ zipWith (\x y -> (x-y)^2) px py

{-@ nearest :: k:Nat -> n:Nat -> CenteringKN k n -> PointN n -> CenterK k @-}
nearest k n centers p = fixme "nearest"

--- >>> minKeyMap (M.fromList [(0, 12), (1, 23), (2, 7), (3,18)])
--- 2
minKeyMap :: (Ord v) => M.Map k v -> k
minKeyMap = minKeyList . M.toList

minKeyList    :: (Ord v) => [(k,v)] -> k
minKeyList xs = fst $ minimumBy (\x1 x2 -> compare (snd x1) (snd x2)) xs

{-@ mergeCluster :: n:Nat -> Cluster -> Cluster -> Cluster @-}
mergeCluster n (n1, p1) (n2, p2) = (n1 + n2, zipWith (+) p1 p2)

centroid n p sz = map (\x -> x `divide` sz) p

{-@ kmeans :: Nat -> k:Nat -> n:Nat ->
              List (PointN n) -> CenteringKN k n -> CenteringKN k n
  @-}
kmeans steps k n ps = repeat steps (kmeans1 k n ps)

repeat :: Int -> (a -> a) -> a -> a
repeat 0 f x = x
repeat n f x = repeat (n-1) f (f x)

{-@ kmeans1 :: k:Int -> n:Int ->
               List (PointN n) -> Centering -> CenteringKN k n
  @-}
kmeans1 k n ps cs = normalize newClusters
  where
    normalize     :: M.Map a Cluster -> M.Map a Point
    normalize     = M.map (\(sz, p) -> centroid n p sz)
    newClusters   = mapReduce fm fr ps
    fm p          = singleton (nearest k n cs p, (1 :: Int, p))
    fr wp1 wp2    = mergeCluster n wp1 wp2

{-@ die :: {v:String | false} -> a @-}
die str = error ("Oops, I died!" ++ str)

{-@ fixme :: {v:String | false} -> a @-}
fixme str = error ("Oops, you didn't fill in the code for: "++ str)

{-@ type TRUE = {v:Bool | v} @-}

{-@ lAssert :: TRUE -> TRUE @-}
lAssert True  = True
lAssert False = die "Assert Fails!"

{-@ divide :: Double -> {v:Int | v /= 0}-> Double @-}
divide     :: Double -> Int -> Double
divide n 0 = die "oops divide by zero"
divide n d = n / (fromIntegral d)
\end{code}
