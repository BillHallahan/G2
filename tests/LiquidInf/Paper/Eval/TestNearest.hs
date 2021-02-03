{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

module Combined ( List
                , test_nearest) where

import Prelude hiding (length, replicate, foldr, foldr1, map, concat, zipWith, repeat)

import qualified Data.Map as M

import Data.List (minimumBy)

infixr 9 :+:

empty     :: List a
add       :: a -> List a -> List a
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
empty = Emp

add x xs = x :+: xs

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

distance n px py = sqrt $ foldr (+) 0 $ zipWith (\x y -> (x-y)^2) px py

nearest k n centers p = pSol
  where
    keyList = M.toList centers
    f x1 x2 = compare (distance n (snd x1) p) (distance n (snd x2) p)
    pSol    = minKeyFuncList keyList f

minKeyFuncList :: (Ord v) => [(k,v)] -> ((k,v) -> (k,v) -> Ordering) -> k
minKeyFuncList xs f = fst $ minimumBy f xs

-- >>> test_nearest
-- 1
test_nearest = nearest 3 2 (M.fromList [(0, p0), (1, p1), (2, p2)]) p
  where
    p, p0, p1, p2 :: Point
    p0 = add 0.0 (add 0.0 empty)
    p1 = add 3.0 (add 0.0 empty)
    p2 = add 0.0 (add 3.0 empty)
    p  = add 2.9 (add 1.1 empty)
