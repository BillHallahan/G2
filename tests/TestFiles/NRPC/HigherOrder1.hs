module HigherOrder1 where

import G2.Symbolic

f :: (Int -> Int) -> Int -> Int
f h x = h (assert (x >= 0) 1)

g :: (Int -> Bool) -> Int -> Int
g h x = assert (h x) 1