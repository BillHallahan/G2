{-@ LIQUID "--no-termination" @-}

module Harmonic (harmonic) where

import Prelude hiding (div)

{-@ type TRUE = {v:Bool | v} @-}

{-@ die :: {v:String | false} -> a @-}
die str = error str

{-@ assert :: TRUE -> a -> a @-}
assert :: Bool -> a -> a
assert True  a = a
assert _ _ = die "violated assert"

div :: Int -> Int -> Int
div x y = assert (y /= 0) (if x < y then 0 else 1 + div (x - y) y)

fold_left :: (b -> a -> b) -> b -> [a] -> b
fold_left f acc xs =
    case xs of
        [] -> acc
        x:xs' -> fold_left f (f acc x) xs'

range :: Int -> Int -> [Int]
range i j = if i > j then [] else let is = range (i + 1) j in i:is

harmonic :: Int -> Int
harmonic n = let ds = range 1 n in
    fold_left (\s k -> s + div 10000 k) 0 ds