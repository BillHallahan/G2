Lists
=====


<div class="hidden">
\begin{code}
{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

-- CHECKBINDER prop_size
-- CHECKBINDER empty
-- CHECKBINDER add
-- CHECKBINDER singleton
-- CHECKBINDER prop_replicate
-- CHECKBINDER prop_map
-- CHECKBINDER foldr1
-- CHECKBINDER prop_zipWith
-- CHECKBINDER prop_concat
 

{-# LANGUAGE DeriveGeneric #-}

module Combined ( List
            , empty
            , add
            , singleton
            , map
            , replicate
            , foldr
            , foldr1
            , zipWith
            , concat
            , die

            , mapReduce
            ) where

import Prelude hiding (length, replicate, foldr, foldr1, map, concat, zipWith, repeat)

import qualified Data.Map as M

import Data.List (minimumBy)

infixr 9 :+:

empty     :: List a
add       :: a -> List a -> List a
singleton :: a -> List a
replicate :: Int -> a -> List a
map       :: (a -> b) -> List a -> List b
zipWith   :: (a -> b -> c) -> List a -> List b -> List c
concat    :: List (List a) -> List a
\end{code}
</div>

\begin{code}
{-@ type TRUE = {v:Bool | v} @-}

{-@ die :: {v:String | false} -> a @-}
die str = error ("Oops, I died!" ++ str)

{-@ lAssert :: TRUE -> TRUE @-}
lAssert True  = True
lAssert False = die "Assert Fails!"

\end{code}

A Sized List Datatype
---------------------

Lets cook up our own `List` data type from scratch:

\begin{code}
data List a = Emp
            | (:+:) a (List a)
              deriving (Eq, Ord, Show)
\end{code}

We can write a **measure** that logically represents
the *size*, i.e. number of elements of a `List`:

\begin{code}
{-@ measure size      :: List a -> Int
    size (Emp)        = 0
    size ((:+:) x xs) = 1 + size xs
  @-}

{-@ invariant {v:List a | 0 <= size v} @-}

{-@ type ListNE a = {v:List a | size v > 0} @-}
\end{code}

It will be helpful to have a few abbreviations. First,
lists whose size is equal to `N`

\begin{code}
{-@ type ListN a N  = {v:List a | size v = N} @-}
\end{code}
and then, lists whose size equals that of *another* list `Xs`:

\begin{code}
{-@ type ListX a Xs = {v:List a | size v = size Xs} @-}
\end{code}

(a) Computing the Length of a List
----------------------------------

Write down a *refined* type for `length`:

\begin{code}
{-@ length :: xs : List a -> {v : Nat | v = size xs} @-}
length            :: List a -> Int
length Emp        = 0
length (x :+: xs) = 1 + length xs
\end{code}

such that the following type checks:

\begin{code}

{-@ prop_size :: TRUE @-}
prop_size  = lAssert (length l3 == 3)

{-@ l3 :: ListN Int 3 @-}
l3     = 3 :+: l2

{-@ l2 :: ListN Int 2 @-}
l2     = 2 :+: l1

{-@ l1 :: ListN Int 1 @-}
l1     = 1 :+: l0

{-@ l0 :: ListN Int 0 @-}
l0     = Emp :: List Int
\end{code}


(b) Constructing Lists
----------------------

Fill in the implementations of the following functions so that
LiquidHaskell verifies respect the given type signatures:

\begin{code}
{-@ empty :: ListN a 0 @-}
empty = Emp

{-@ add :: a -> xs:List a -> ListN a {1 + size xs} @-}
add x xs = x :+: xs

{-@ singleton :: a -> ListN a 1 @-}
singleton x = x :+: empty
\end{code}

(c) Replicating Values
----------------------

Fill in the code, and update the refinement type specification
for `replicate n x` which should return a `List` `n` copies of
the value `x`:

\begin{code}
{-@ replicate :: n : Nat -> a -> ListN a n @-}
replicate n x
  | n == 0    = empty
  | otherwise = x :+: replicate (n - 1) x
\end{code}

When you are done, the following assertion should be verified by LH.

\begin{code}
{-@ prop_replicate :: Nat -> a -> TRUE @-}
prop_replicate n x = lAssert (n == length (replicate n x))
\end{code}

(d) Map
-------

Fix the specification for `map` such that the assertion in `prop_map`
is verified by LH. (This will require you to first complete part (a) above.)

\begin{code}
{-@ map :: (a -> b) -> xa : List a -> { xb : List b | size xa = size xb } @-}
map f Emp        = Emp
map f (x :+: xs) = f x :+: map f xs

{-@ prop_map :: (a -> b) -> List a -> TRUE @-}
prop_map f xs = lAssert (length xs == length (map f xs))
\end{code}

(e) Fold
--------

Fix the specification for `foldr1` so that the call to `die` is
verified by LH:

\begin{code}
{-@ foldr1 :: (a -> a -> a) -> { xs : List a | size xs > 0 } -> a @-}
foldr1 op (x :+: xs) = foldr op x xs
foldr1 op Emp        = die "Cannot call foldr1 with empty list"

foldr :: (a -> b -> b) -> b -> List a -> b
foldr _  b Emp        = b
foldr op b (x :+: xs) = x `op` foldr op b xs
\end{code}

(f) ZipWith
-----------

Fix the specification of `zipWith` so that LH verifies:

+ The call to `die` inside `zipWith` and
+ The assert inside `prop_zipwith`.

\begin{code}
{-@ zipWith :: (a -> b -> c) -> xa : List a -> { xb : List b | size xa = size xb } -> { xc : List c | size xa = size xc } @-}
zipWith _ Emp Emp               = Emp
zipWith f (x :+: xs) (y :+: ys) = f x y :+: zipWith f xs ys
zipWith f _          _          = die  "Bad call to zipWith"

{-@ prop_zipWith :: Num a => List a -> TRUE @-}
prop_zipWith xs = lAssert (length xs == length x2s)
  where
    x2s         = zipWith (+) xs xs
\end{code}

(g) List Concatenation *(Hard?)*
--------------------------------

Fill in the (refinement type) specification and
implementation for the function `concat` such that
when you are done, the assert inside `prop_concat`
is verified by LH. Feel free to write any other code
or specification (types, measures) that you need.

\begin{code}
{-@ measure sizeXs          :: List (List a) -> Int
    sizeXs (Emp)            = 0
    sizeXs ((:+:) xs xss)   = size xs + sizeXs xss
  @-}
    

{-@ concat :: x:List (List a) -> {v:List a | sizeXs x == size v } @-}
concat Emp = Emp
concat (xs :+: Emp) = xs
concat (xs :+: (ys :+: xss)) = concat ((append xs ys) :+: xss)

{-@ append :: x:List a -> y:List a -> {z:List a | size x + size y == size z } @-}
append :: List a -> List a -> List a
append xs Emp = xs
append Emp ys = ys
append (x :+: xs) ys = x :+: append xs ys

{-@ prop_concat :: TRUE @-}
prop_concat = lAssert (length (concat xss) == 6)
  where
    xss     = l0 :+: l1 :+: l2 :+: l3 :+: Emp

{-@ prop_concat2 :: TRUE @-}
prop_concat2 = lAssert (length (concat yss) == 0)
  where
    yss     = l0 :+: l0 :+: l0 :+: Emp
\end{code}

========================================
Map-Reduce
========================================

<div class="hidden">
\begin{code}

expand   :: (a -> List (k, v)) -> List a -> List (k, v)
group    :: (Ord k) => List (k, v) -> M.Map k (List v)
collapse :: (v -> v -> v) -> M.Map k (List v) -> M.Map k v
\end{code}
</div>

The following is a super simplified implementation of
[Map-Reduce](http://en.wikipedia.org/wiki/MapReduce)
using the [Lists](List.lhs) and `Data.Map`.

\begin{code}
mapReduce :: (Ord k) => (a -> List (k, v))
                     -> (v -> v -> v)
                     -> List a
                     -> M.Map k v

mapReduce fm fr xs = kvm
  where
    kvs   = expand      fm xs     -- step 1
    kvsm  = group       kvs       -- step 2
    kvm   = collapse fr kvsm      -- step 3
\end{code}

**The Problem** If you solved `foldr1` then you should
get a single type error below, in the call to `foldr1`
in `collapse`. Fix the error by **modifying the
refinement type specifications** only (do not modify any code).

**Note:** This problem requires you to have solved the
`foldr1` problem from [List.lhs](List.lhs); otherwise
no points.

Next, we briefly describe and show each step of the
`mapReduce` function.

Step 1: Map Elements into Key-Value Lists
-----------------------------------------

\begin{code}
{-@ expand  :: (a -> List (k, v)) -> List a -> List (k, v) @-}
expand f xs = concat (map f xs)
\end{code}

Step 2: Group By Key
--------------------

\begin{code}
{-@ group :: (Ord k) => List (k, v) -> M.Map k (ListNE v) @-}
group     = foldr addKV  M.empty

addKV (k,v) m = M.insert k vs' m
  where
    vs'       = add v (M.findWithDefault empty k m)
\end{code}

Step 3: Reduce Each Key to Single Value
---------------------------------------

\begin{code}
{-@ collapse  :: (v -> v -> v) -> M.Map k (ListNE v) -> M.Map k v @-}
collapse f = M.map (foldr1 f)

toList :: M.Map k v -> List (k, v)
toList = M.foldrWithKey (\k v acc -> add (k, v) acc) empty
\end{code}

========================================
KMeans
========================================

<div class="hidden">
\begin{code}


centroid :: Int -> Point -> Int -> Point
distance :: Int -> Point -> Point -> Double
nearest   :: Int -> Int -> Centering -> Point -> Center
mergeCluster :: Int -> Cluster -> Cluster -> Cluster
kmeans1   :: Int -> Int -> List Point -> Centering -> Centering
kmeans    :: Int -> Int -> Int -> List Point -> Centering -> Centering
\end{code}
</div>

Next, lets use our `MapReduce` library to implement
[K-Means Clustering](http://en.wikipedia.org/wiki/K-means_clustering)


From Assert.lhs:

Divide By Zero
--------------

Finally, lets write a *safe* divide by zero operator (that we will use later)

\begin{code}
{-@ divide :: Double -> {v:Int | v /= 0}-> Double @-}
divide :: Double -> Int -> Double
divide n 0 = die "oops divide by zero"
divide n d = n / (fromIntegral d)
\end{code}

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
{-@ distance :: n:Nat -> px:Point -> PointN {size px} -> Double @-}
distance n px py = sqrt $ foldr (+) 0 $ zipWith (\x y -> (x-y)^2) px py
\end{code}

(b) Map Points To Nearest Center
--------------------------------

Use `distance` to fill in the **implementation** of `nearest`
so that LH verifies the given type signature.

\begin{code}
{-@ nearest :: k:Nat -> n:Nat -> CenteringKN k n -> PointN n -> CenterK k @-}
nearest k n centers p = pSol
  where
    keyList = M.toList centers
    f x1 x2 = compare (distance n (snd x1) p) (distance n (snd x2) p)
    pSol    = minKeyFuncList keyList f

{-@ minKeyFuncList :: (Ord v) => [(k,v)] -> ((k,v) -> (k,v) -> Ordering) -> k @-}
minKeyFuncList :: (Ord v) => [(k,v)] -> ((k,v) -> (k,v) -> Ordering) -> k
minKeyFuncList xs f = fst $ minimumBy f xs
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
{-@ mergeCluster :: n:Nat -> ClusterN n -> ClusterN n -> ClusterN n @-}
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

