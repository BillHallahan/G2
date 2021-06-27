{-@ LIQUID "--no-termination" @-}

module Halves (prop_halve_append) where

import Data.Set

{-@ type True = {v:Bool | v} @-}

{-@ prop_halve_append  :: Int -> [a] -> True @-}
prop_halve_append n xs = elts xs == elts xs'
  where
    xs'      =  append ys zs
    (ys, zs) =  halve n xs

halve            :: Int -> [a] -> ([a], [a])
halve 0 xs       = ([], xs)
halve n (x:y:zs) = (x:xs, y:ys) where (xs, ys) = halve (n-1) zs
halve _ xs       = ([], xs)

append []     ys = ys
append (x:xs) ys = x : append xs ys

elts        :: (Ord a) => [a] -> Set a
elts []     = empty
elts (x:xs) = singleton x `union` elts xs

