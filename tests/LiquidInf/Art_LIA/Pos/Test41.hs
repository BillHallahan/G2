{-@ LIQUID "--no-termination" @-}

module Reverse (reverse) where

import Prelude hiding (length, reverse)

{-@ reverse :: x:[a] -> {r : [a] | ((-len x) + len r == 0)} @-}
reverse xs        = go [] xs

go acc []     = acc
go acc (x:xs) = go (x:acc) xs