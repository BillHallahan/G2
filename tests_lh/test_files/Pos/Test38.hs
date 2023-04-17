module Combined ( List, test_nearest) where

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

add       :: a -> List a -> List a
add x xs = x :+: xs

foldr :: (a -> b -> b) -> b -> List a -> b
foldr _  b Emp        = b
foldr op b (x :+: xs) = x `op` foldr op b xs

zipWith   :: List a -> List a -> List a
zipWith Emp Emp               = Emp
zipWith (x :+: xs) (y :+: ys) = x :+: zipWith xs ys
zipWith _          _          = die  "Bad call to zipWith"

-- | N-Dimensional Point
type Point   = List Double

distance :: Int -> Point -> Point -> Double
distance n px py = foldr (+) 0 $ zipWith px py

nearest   :: Int -> Int -> M.Map Int Point -> Point -> Int
nearest k n centers p = fst $ minimumBy f (M.toList centers)
  where
    f x1 x2 = compare (distance n (snd x1) p) (distance n (snd x2) p)

test_nearest = nearest 2 2 (M.fromList [(0, p0), (1, p1)]) p
  where
    p, p0, p1 :: Point
    p0 = add 0.0 (add 0.0 Emp)
    p1 = add 3.0 (add 0.0 Emp)
    p  = add 2.9 (add 1.1 Emp)
