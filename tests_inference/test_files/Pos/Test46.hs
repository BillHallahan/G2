{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

module Test46 ( List, test_nearest) where

import Prelude hiding (zipWith)

import Data.List (minimumBy)
import qualified Data.List as L

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

zipWith   :: List Double -> List Double -> Double
zipWith Emp Emp               = 0
zipWith (x :+: xs) (y :+: ys) = zipWith xs ys
zipWith _          _          = die  "Bad call to zipWith"

nearest   :: [List Double] -> List Double -> List Double
nearest centers p = minKeyFuncList centers f
  where
    f x1 x2 = compare (zipWith x1 p) (zipWith x2 p)

minKeyFuncList :: [List Double] -> (List Double -> List Double -> Ordering) -> List Double
minKeyFuncList xs f =  minimumBy f xs

test_nearest = nearest [p] p
  where
    p :: List Double
    p  = (0 :+: Emp)