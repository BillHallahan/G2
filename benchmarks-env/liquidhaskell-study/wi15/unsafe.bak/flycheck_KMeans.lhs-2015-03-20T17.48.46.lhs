K-Means Clustering
==================


<div class="hidden">
\begin{code}
{-@ LIQUID "--short-names"    @-}
{-@ LIQUID "--no-termination" @-}

module KMeans (kmeans, kmeans1, nearest, mergeCluster) where

import Data.List (minimumBy)
import MapReduce
import Assert
import List
import Prelude hiding (map, repeat, foldr, zipWith)
import qualified Data.Map as M

distance :: Int -> Point -> Point -> Double
nearest   :: Int -> Int -> Centering -> Point -> Center
mergeCluster :: Int -> Cluster -> Cluster -> Cluster
kmeans1   :: Int -> Int -> List Point -> Centering -> Centering
kmeans    :: Int -> Int -> Int -> List Point -> Centering -> Centering
\end{code}
</div>

Next, lets use our `MapReduce` library to implement
[K-Means Clustering](http://en.wikipedia.org/wiki/K-means_clustering)


Points and Clusters
-------------------

First, lets define the various types that model the key entities in clustering.


\begin{code}
-- | N-Dimensional Point
type Point   = List Double

{-@ type PointN N = ListN Double N @-}
\end{code}

**A Center** is a number between `0` and `k` (written `CenterK k`).

\begin{code}
type Center  = Int
{-@ type CenterK K = {v:Int | 0 <= v && v < K} @-}
\end{code}

**A Centering** is a map from `Center`s to `Point`s. Our clustering algorithm
will aim to group a (large) set of `Point`s into `k` representatives. Thus, a
*k-n-Centering* is a map from `CenterK k` to `PointN n`:

\begin{code}
type Centering = M.Map Center Point
{-@ type CenteringKN K N = M.Map (CenterK K) (PointN N) @-}
\end{code}

**A Cluster** is a pair of a *number* of points (denoting the cluster size)
and the *co-ordinates* denoting the (sum of) the co-ordinates of all the points
in the cluster. We represent `n`-dimensional clusters as `ClusterN n`;  note that
the cluster size is *strictly positive* as we will never represent empty clusters.

\begin{code}
type Cluster = (Int, Point)

{-@ type ClusterN N = (Pos, PointN N) @-}
{-@ type Pos        = {v:Int | v > 0} @-}
\end{code}

(a) Computing Euclidean Distance
--------------------------------

If you did the `zipWith` problem, then you should see an error in
the implementation of `distance` which computes the
[Euclidean Distance](http://en.wikipedia.org/wiki/Euclidean_distance)
between two points. Fix the **specification** (not the code) of `distance` so
that the code is verified by LH:

\begin{code}
{-@ distance :: n:Nat -> x:Point -> Point -> Double @-}
distance n px py = sqrt $ foldr (+) 0 $ zipWith (\x y -> (x-y)^2) px py
\end{code}

(b) Map Points To Nearest Center
--------------------------------

Use `distance` to fill in the **implementation** of `nearest`
so that LH verifies the given type signature.

\begin{code}
{-@ nearest :: k:Nat -> n:Nat -> CenteringKN k n -> PointN n -> CenterK k @-}
nearest k n centers p = fixme "nearest"
\end{code}

You may want to use the helper `minKeyMap` that computes the key
with the smallest value in a `Map`:

\begin{code}
--- >>> minKeyMap (M.fromList [(0, 12), (1, 23), (2, 7), (3,18)])
--- 2
minKeyMap  :: (Ord v) => M.Map k v -> k
minKeyMap  = minKeyList . M.toList

minKeyList    :: (Ord v) => [(k,v)] -> k
minKeyList xs = fst $ minimumBy (\x1 x2 -> compare (snd x1) (snd x2)) xs
\end{code}

When you are done, you should get the following behavior:


\begin{code}
-- >>> test_nearest
-- 1
test_nearest = nearest 3 2 (M.fromList [(0, p0), (1, p1), (2, p2)]) p
  where
    p, p0, p1, p2 :: Point
    p0 = add 0.0 (add 0.0 empty)
    p1 = add 3.0 (add 0.0 empty)
    p2 = add 0.0 (add 3.0 empty)
    p  = add 2.9 (add 1.1 empty)
\end{code}

(c) Reduce Clusters
-------------------

Fix the **specification** below so that that LH verifies `mergeCluster`
which takes two `Cluster` and merges them by adding up their points
and centers. (Leave the code unmodified).

\begin{code}
{-@ mergeCluster :: n:Nat -> Cluster -> Cluster -> Cluster @-}
mergeCluster n (n1, p1) (n2, p2) = (n1 + n2, zipWith (+) p1 p2)
\end{code}

**Note:** The code above uses `zipWith`; so you will only see the error
and be able to fix it, *after* you solve that problem.

(d) Convert Cluster into Centroid Point
---------------------------------------

The `centroid` function converts a `Cluster` into a single `Point` by
dividing each co-ordinate with the cluster size. Fix the **specification**
of `centroid` so that LH verifies the call to `divide`:

\begin{code}
centroid n p sz = map (\x -> x `divide` sz) p
\end{code}

**Note:** The code below uses `map` from `List.lhs`; and hence
your solution will only work if you solved that problem first.


(e) Iterative Clustering
--------------------

The Kmeans clustering algorithm is shown below:



\begin{code}
{-@ kmeans :: Nat -> k:Nat -> n:Nat ->
              List (PointN n) -> CenteringKN k n -> CenteringKN k n
  @-}
kmeans steps k n ps = repeat steps (kmeans1 k n ps)

repeat :: Int -> (a -> a) -> a -> a
repeat 0 f x = x
repeat n f x = repeat (n-1) f (f x)
\end{code}

In essence we start with an initial `k` centering, and repeatedly update it by calling
`kmeans1` which takes as input a list of `n` dimensional points, a centering and returns
a new centering (with `k` centers and `n` dimensional points). The new centers are computed by:

1. Mapping each point to its `nearest` center,
2. Grouping all the points mapped to a center into a new cluster,
3. Reducing the clusters by adding up all the points inside them, and
4. Normalizing each cluster to its `centroid`.

\begin{code}
{-@ kmeans1 :: k:Nat -> n:Nat ->
               List (PointN n) -> CenteringKN k n -> CenteringKN k n
  @-}
kmeans1 k n ps cs = normalize newClusters
  where
    normalize     :: M.Map a Cluster -> M.Map a Point
    normalize     = M.map (\(sz, p) -> centroid n p sz)
    newClusters   = mapReduce fm fr ps
    fm p          = singleton (nearest k n cs p, (1 :: Int, p))
    fr wp1 wp2    = mergeCluster n wp1 wp2
\end{code}

Fix the code and specifications above so that LH verifies the the specification for `kmeans` and `kmeans1`
(i.e. verifies this entire module.)

**Hint:** If you did the above problems correctly, you should have to do nothing here.
Otherwise, think about what type `normalize` should have and try to work backwards
to verify that type.

