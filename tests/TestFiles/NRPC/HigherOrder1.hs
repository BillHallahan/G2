module HigherOrder1 where

import G2.Symbolic

f :: (Int -> Int) -> Int -> Int
f h x = h (assert (x >= 0) 1)