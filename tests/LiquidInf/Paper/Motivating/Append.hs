{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

module Concat where

import Prelude hiding (length, concat)

{-@ measure size @-}
size :: [a] -> Int
size [] = 0
size (x:xs) = 1 + size xs

{-@ invariant {v:[a] | 0 <= size v} @-}
{-@ invariant {v:[a] | len v == size v} @-}

{-@ append :: xs:[a] -> ys:[a] -> { zs:[a] | size xs == size zs } @-}
append :: [a] -> [a] -> [a]
append xs [] = xs
append [] ys = ys
append (x:xs) ys = x:append xs ys

{-@ prop_append :: [a] -> [a] -> { v:Bool | v } @-}
prop_append :: [a] -> [a] -> Bool
prop_append xs ys =
    size (append xs ys) >= size xs
