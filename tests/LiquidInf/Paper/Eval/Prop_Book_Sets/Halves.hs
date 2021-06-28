{-@ LIQUID "--no-termination" @-}

module Halves (prop_halve_append) where

import Data.Set

{-@ type True = {v:Bool | v} @-}

{-@ prop_halve_append  :: Int -> [Int] -> True @-}
prop_halve_append :: Int -> [Int] -> Bool
prop_halve_append n xs = elts xs == elts xs'
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

elts        :: [Int] -> Set Int
elts []     = empty
elts (x:xs) = singleton x `union` elts xs

