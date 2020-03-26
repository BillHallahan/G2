{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

module ListQualif ( List ) where

import Prelude hiding (map)
import Data.List (minimumBy)

infixr 9 :+:

{-@ die :: {v:String | false} -> a @-}
die str = error ("Oops, I died!" ++ str)

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

divide :: Double -> Int -> Double
divide n 0 = die "oops divide by zero"
divide n d = n

type Point   = List Double
{-@ type PointN = {v:List Double | size v = 1} @-}

centroid :: Point -> Int -> Point
centroid p sz = map (\x -> x `divide` sz) p

{-@ normalize :: { x:Int | x /= 0} -> PointN -> PointN @-}
normalize :: Int -> Point -> Point
normalize sz p = centroid p sz
