{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

module Combined ( List, kmeans1) where

import Prelude hiding (length, replicate, foldr, foldr1, map, concat, zipWith, repeat)
import qualified Data.Map as M
import Data.List (minimumBy)

infixr 9 :+:

{-@ type TRUE = {v:Bool | v} @-}

{-@ die :: {v:String | false} -> a @-}
die str = error ("Oops, I died!" ++ str)

data List a = Emp
            | (:+:) a (List a)
              deriving (Eq, Ord, Show)

{-@ measure size      :: List a -> Int
    size (Emp)        = 0
    size ((:+:) x xs) = 1 + size xs
  @-}

{-@ invariant {v:List a | 0 <= size v} @-}

{-@ type ListN a N  = {v:List a | size v = N} @-}

map       :: (a -> b) -> List a -> List b
map f Emp        = Emp
map f (x :+: xs) = f x :+: map f xs

foldr1 op (x :+: xs) = foldr op x xs
foldr1 op Emp        = die "Cannot call foldr1 with empty list"

foldr :: (a -> b -> b) -> b -> List a -> b
foldr _  b Emp        = b
foldr op b (x :+: xs) = x `op` foldr op b xs

zipWith   :: (a -> b -> c) -> List a -> List b -> List c
zipWith _ Emp Emp               = Emp
zipWith f (x :+: xs) (y :+: ys) = f x y :+: zipWith f xs ys
zipWith f _          _          = die  "Bad call to zipWith"

mapReduce :: (Ord k) => (a -> (k, v))
                     -> (v -> v -> v)
                     -> List a
                     -> M.Map k v
mapReduce fm fr xs = M.map (foldr1 fr) kvsm
  where
    kvs   = map      fm xs     -- step 1
    kvsm  = foldr addKV  M.empty       kvs       -- step 2

addKV (k,v) m = M.insert k vs' m
  where
    vs'       = v :+: (M.findWithDefault Emp k m)

-- | N-Dimensional Point
type Point   = List Double

type Centering = M.Map Int Point
{-@ type CenteringKN K N = M.Map {v:Int | 0 <= v && v < K} (ListN Double N) @-}

nearest   :: Int -> Int -> Centering -> Point -> Int
nearest k n centers p = fst $ minimumBy (\_ _ -> LT) (M.toList centers)

{-@ kmeans1 :: k:Nat -> n:Nat ->
              List (ListN Double n) -> CenteringKN k n -> CenteringKN k n @-}
kmeans1   :: Int -> Int -> List Point -> Centering -> Centering
kmeans1 k n ps cs = newClusters
  where
    newClusters   = mapReduce fm fr ps
    fm p          = (nearest k n cs p,  p)
    fr wp1 wp2    = wp1
