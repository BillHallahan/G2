{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

module Test44 ( List, mapReduce) where

import Prelude hiding (foldr, foldr1)

{-@ die :: {v:String | false} -> a @-}
die str = error ("Oops, I died!" ++ str)

data List a = Emp
            | C a (List a)

{-@ measure size      :: List a -> Int
    size (Emp)        = 0
    size (C x xs) = 1 + size xs @-}

{-@ invariant {v:List a | 0 <= size v} @-}

foldr1 (C x xs) = foldr (\y _ -> y) x xs
foldr1 Emp        = die "Cannot call foldr1 with empty list"

foldr :: (a -> b -> b) -> b -> List a -> b
foldr _  b Emp        = b
foldr op b (C x xs) = x `op` foldr op b xs

mapReduce :: List v -> [v]
mapReduce xs = map (\v -> foldr1 v) (foldr (\v m -> C v Emp:m) [] xs)