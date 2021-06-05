{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

-- timeout = 300

module ListQualif ( List ) where

import Prelude hiding (length, replicate, foldr, foldr1, map, concat, zipWith, repeat)
import Data.List (minimumBy)
import qualified Data.Map as M

infixr 9 :+:

map       :: (a -> b) -> List a -> List b
zipWith   :: (a -> b -> c) -> List a -> List b -> List c
concat    :: List (List a) -> List a

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

{-@ l1 :: ListN Int 1 @-}
l1     = 1 :+: l0

{-@ l0 :: ListN Int 0 @-}
l0     = Emp :: List Int

map f Emp        = Emp
map f (x :+: xs) = f x :+: map f xs

{-@ prop_map :: (a -> b) -> List a -> TRUE @-}
prop_map f xs = lAssert (length xs == length (map f xs))

foldr1 op (x :+: xs) = foldr op x xs
foldr1 op Emp        = die "Cannot call foldr1 with empty list"

foldr :: (a -> b -> b) -> b -> List a -> b
foldr _  b Emp        = b
foldr op b (x :+: xs) = x `op` foldr op b xs

zipWith _ Emp Emp               = Emp
zipWith f (x :+: xs) (y :+: ys) = f x y :+: zipWith f xs ys
zipWith f _          _          = die  "Bad call to zipWith"

{-@ measure sizeXs          :: List (List a) -> Int
    sizeXs (Emp)            = 0
    sizeXs ((:+:) xs xss)   = size xs + sizeXs xss
  @-}

concat Emp = Emp
concat (xs :+: Emp) = xs
concat (xs :+: (ys :+: xss)) = concat ((append xs ys) :+: xss)

{-@ append :: xs:List a -> ys:List a -> { zs:List a | size zs == size xs + size ys } @-}
append :: List a -> List a -> List a
append xs Emp = xs
append Emp ys = ys
append (x :+: xs) ys = x :+: append xs ys

{-@ prop_concat :: TRUE @-}
prop_concat = lAssert (length (concat xss) == 1)
  where
    xss     = l0 :+: l1 :+: Emp

expand   :: (a -> List (k, v)) -> List a -> List (k, v)
group    :: (Ord k) => List (k, v) -> M.Map k (List v)
collapse :: (v -> v -> v) -> M.Map k (List v) -> M.Map k v

mapReduce :: (Ord k) => (a -> List (k, v))
                     -> (v -> v -> v)
                     -> List a
                     -> M.Map k v
mapReduce fm fr xs = kvm
  where
    kvs   = expand      fm xs     -- step 1
    kvsm  = group       kvs       -- step 2
    kvm   = collapse fr kvsm      -- step 3

expand f xs = concat (map f xs)

group     = foldr addKV  M.empty

addKV (k,v) m = M.insert k vs' m
  where
    vs'       = v :+: (M.findWithDefault Emp k m)

collapse f = M.map (foldr1 f)

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

distance n px py = sqrt $ foldr (+) 0 $ zipWith (\x y -> (x-y)^2) px py

{-@ nearest :: k:Nat -> n:Nat -> CenteringKN k n -> PointN n -> CenterK k @-}
nearest k n centers p = pSol
  where
    keyList = M.toList centers
    f x1 x2 = compare (distance n (snd x1) p) (distance n (snd x2) p)
    pSol    = minKeyFuncList keyList f

minKeyFuncList :: (Ord v) => [(k,v)] -> ((k,v) -> (k,v) -> Ordering) -> k
minKeyFuncList xs f = fst $ minimumBy f xs

{-@ mergeCluster :: n:Nat -> ClusterN n -> ClusterN n -> ClusterN n @-}
mergeCluster n (n1, p1) (n2, p2) = (n1 + n2, p1)

{-@ kmeans :: Nat -> k:Nat -> n:Nat ->
              List (PointN n) -> CenteringKN k n -> CenteringKN k n @-}
kmeans steps k n ps = repeat steps (kmeans1 k n ps)

repeat :: Int -> (a -> a) -> a -> a
repeat 0 f x = x
repeat n f x = repeat (n-1) f (f x)

{-@ kmeans1 :: k:Nat -> n:Nat ->
               List (PointN n) -> CenteringKN k n -> CenteringKN k n @-}
kmeans1 k n ps cs = normalize newClusters
  where
    normalize     :: M.Map a Cluster -> M.Map a Point
    normalize     = M.map (\(sz, p) -> p)
    newClusters   = mapReduce fm fr ps
    fm p          = (nearest k n cs p, (1 :: Int, p)) :+: Emp
    fr wp1 wp2    = mergeCluster n wp1 wp2
