
{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

module Combined ( List ) where

import Prelude hiding (length, replicate, foldr, foldr1, map, concat, zipWith, repeat)

import qualified Data.Map as M

import Data.List (minimumBy)

infixr 9 :+:

map       :: (a -> b) -> List a -> List b
zipWith   :: (a -> b -> c) -> List a -> List b -> List c

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

{-@ type ListNE a = {v:List a | size v > 0} @-}

{-@ type ListN a N  = {v:List a | size v = N} @-}

{-@ type ListX a Xs = {v:List a | size v = size Xs} @-}

length            :: List a -> Int
length Emp        = 0
length (x :+: xs) = 1 + length xs



map f Emp        = Emp
map f (x :+: xs) = f x :+: map f xs


foldr1 op (x :+: xs) = foldr op x xs
foldr1 op Emp        = die "Cannot call foldr1 with empty list"

foldr :: (a -> b -> b) -> b -> List a -> b
foldr _  b Emp        = b
foldr op b (x :+: xs) = x `op` foldr op b xs


zipWith _ Emp Emp               = Emp
zipWith f (x :+: xs) (y :+: ys) = f x y :+: zipWith f xs ys
zipWith f _          _          = die  "Bad call to zipWith"


distance :: Int -> Point -> Point -> Double
nearest   :: Int -> Int -> Centering -> Point -> Center

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


{-@ distance :: Int -> px:(List Double) -> {lq_tmp$x##4 : (List {_ : Double | false}) | ((-size px) >= 0)} -> Double@-}
distance n px py = sqrt $ foldr (+) 0 $ zipWith (\x y -> (x-y)^2) px py


{-@ nearest :: k:Int
            -> n:Int
            -> (M.Map {c : Int | (k > c) && (c >= 0)} {xs : (List Double) | (size xs == n)})
            -> {ys : (List Double) | (n == size ys)}
            -> {r : Int | (k > r) && (r >= 0)} @-}
nearest k n centers p = pSol
  where
    keyList = M.toList centers
    f x1 x2 = compare (distance n (snd x1) p) (distance n (snd x2) p)
    pSol    = minKeyFuncList keyList f

minKeyFuncList :: (Ord v) => [(k,v)] -> ((k,v) -> (k,v) -> Ordering) -> k
minKeyFuncList xs f = fst $ minimumBy f xs

