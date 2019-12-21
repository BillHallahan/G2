{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

module List ( List
            , zipWith
            ) where

import Prelude hiding (length, replicate, foldr, foldr1, map, concat, zipWith)

infixr 9 :+:

zipWith   :: (Int -> Int) -> List -> List

{-@ type TRUE = {v:Bool | v} @-}

{-@ die :: {v:String | false} -> a @-}
die str = error ("Oops, I died!" ++ str)

{-@ lAssert :: TRUE -> TRUE @-}
lAssert True  = True
lAssert False = die "Assert Fails!"

data List = Emp
          | (:+:) Int List
              deriving (Eq, Ord, Show)

{-@ measure size      :: List -> Int
    size (Emp)        = 0
    size ((:+:) x xs) = 1 + size xs
  @-}

{-@ invariant {v:List | 0 <= size v} @-}

{-@ length :: xs : List -> Int @-}
length            :: List -> Int
length Emp        = 0
length (x :+: xs) = 1 + length xs

{-@ zipWith :: (Int -> Int) -> xa : List -> List @-}
zipWith _ _               = Emp

{-@ prop_zipWith :: List -> TRUE @-}
prop_zipWith :: List -> Bool
prop_zipWith xs = lAssert (0 == length x2s)
  where
    x2s         = zipWith f xs


f :: Int -> Int
f x = x