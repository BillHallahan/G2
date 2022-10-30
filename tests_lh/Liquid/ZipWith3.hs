{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

module List ( List
            , zipWith
            ) where

import Prelude hiding (length, replicate, foldr, foldr1, map, concat, zipWith)

infixr 9 :+:

zipWith :: (Int -> Int -> Int) -> List -> List

{-@ type TRUE = {v:Bool | v} @-}

data List = Emp
          | (:+:) Int List
              deriving (Eq, Ord, Show)

{-@ length :: xs : List -> Int @-}
length            :: List -> Int
length Emp        = 0
length (x :+: xs) = 1 + length xs

{-@ zipWith :: (Int -> Int -> Int) -> List -> List @-}
zipWith _ Emp  = Emp
zipWith f (x :+: xs) = f x x :+: zipWith f xs

{-@ prop_zipWith :: List -> TRUE @-}
prop_zipWith :: List -> Bool
prop_zipWith xs = length xs == length (zipWith (+) xs)