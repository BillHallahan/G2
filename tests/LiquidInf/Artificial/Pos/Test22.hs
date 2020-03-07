{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

module ListQualif ( List ) where

import Prelude hiding (length, replicate, foldr, foldr1, map, concat, zip)
import Data.List (foldl1)
import qualified Data.Map as M

infixr 9 :+:

{-@ die :: {v:String | false} -> a @-}
die str = error ("Oops, I died!" ++ str)

data List = Emp | (:+:) Double List

{-@ measure size      :: List -> Int
    size (Emp)        = 0
    size ((:+:) x xs) = 1 + size xs
  @-}

{-@ invariant {v:List | 0 <= size v} @-}

{-@ type ListN N  = {v:List | size v = N} @-}

foldr :: Double -> List -> Double
foldr b Emp        = b
foldr b (x :+: xs) = x + foldr b xs

{-@ zip   :: xs:List -> { ys:List | size xs == size ys} -> List @-}
zip   :: List -> List -> List
zip Emp Emp               = Emp
zip (x :+: xs) (y :+: ys) = x :+: Emp
zip _          _          = die  "Bad call to zipWith"

{-@ type IntK K = {v:Int | 0 <= v && v < K} @-}

distance :: Int -> List -> List -> Double
distance n px py = foldr 0 $ zip px py

{-@ nearest :: k:Nat -> n:Nat -> [(IntK k, ListN n)] -> ListN n -> IntK k @-}
nearest   :: Int -> Int -> [(Int, List)] -> List -> Int
nearest k n centers p = pSol
  where
    f x1 x2 = compare (distance n (snd x1) p) (distance n (snd x2) p)
    pSol    = fst $ foldl1 min' centers

    min' x y = case f x y of
                        GT -> y
                        _  -> x