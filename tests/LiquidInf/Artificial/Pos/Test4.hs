{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

module ListQualif ( List ) where

import Prelude hiding (map)
import Data.List (minimumBy)

infixr 9 :+:

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

{-@ divide :: Double -> { x:Int | x /= 0 } -> Double @-}
divide :: Double -> Int -> Double
divide n 0 = error "divide by zero"
divide n d = n

type Point   = List Double
{-@ type PointN n = {v:List Double | size v = n} @-}

centroid :: Point -> Int -> Point
centroid p sz = map (\x -> x `divide` sz) p

{-@ normalize :: { x:Int | x /= 0} -> v:List Double -> { w:List Double | size v == size w} @-}
normalize :: Int -> Point -> Point
normalize sz p = centroid p sz
