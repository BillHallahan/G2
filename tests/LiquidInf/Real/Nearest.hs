{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

module ListQualif ( List ) where

import Prelude hiding (length, replicate, foldr, foldr1, map, concat, zipWith)
import Data.List (minimumBy)
import qualified Data.Map as M

infixr 9 :+:

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

foldr :: (a -> b -> b) -> b -> List a -> b
foldr _  b Emp        = b
foldr op b (x :+: xs) = x `op` foldr op b xs

zipWith   :: (a -> b -> c) -> List a -> List b -> List c
zipWith _ Emp Emp               = Emp
zipWith f (x :+: xs) (y :+: ys) = f x y :+: zipWith f xs ys
zipWith f _          _          = die  "Bad call to zipWith"

-- | N-Dimensional Point
type Point   = List Double

{-@ type PointN N = ListN Double N @-}

type Center  = Int
{-@ type CenterK K = {v:Int | 0 <= v && v < K} @-}

type Centering = M.Map Center Point
{-@ type CenteringKN K N = M.Map (CenterK K) (PointN N) @-}

distance :: Int -> Point -> Point -> Double
distance n px py = sqrt $ foldr (+) 0 $ zipWith (\x y -> (x-y)^2) px py

{-@ nearest :: k:Nat -> n:Nat -> CenteringKN k n -> PointN n -> CenterK k @-}
nearest   :: Int -> Int -> Centering -> Point -> Center
nearest k n centers p = pSol
  where
    keyList = M.toList centers
    f x1 x2 = compare (distance n (snd x1) p) (distance n (snd x2) p)
    pSol    = minKeyFuncList keyList f

minKeyFuncList :: (Ord v) => [(k,v)] -> ((k,v) -> (k,v) -> Ordering) -> k
minKeyFuncList xs f = fst $ minimumBy f xs
