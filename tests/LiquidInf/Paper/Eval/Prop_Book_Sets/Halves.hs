
module Halves (prop_halve_append) where

import Data.Set

{-@ type True = {v:Bool | v} @-}

{-@ prop_halve_append  :: Int -> xs:[Int] -> { ys:[Int] | listElts xs == listElts ys } @-}
prop_halve_append :: Int -> [Int] -> [Int]
prop_halve_append n xs = xs'
  where
    xs'      =  append ys zs
    (ys, zs) =  halve n xs

halve            :: Int -> [Int] -> ([Int], [Int])
halve 0 xs       = ([], xs)
halve n (x:y:zs) = (x:xs, y:ys) where (xs, ys) = halve (n-1) zs
halve _ xs       = ([], xs)

append :: [Int] -> [Int] -> [Int]
append []     ys = ys
append (x:xs) ys = x : append xs ys

{-@ LIQUID "--no-termination" @-}
