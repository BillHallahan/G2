{-@ LIQUID "--prune-unsorted" @-}

module Concat where

import Prelude hiding (concat)

{-@ measure size @-}
size :: [a] -> Int
size [] = 0
size (x:xs) = 1 + size xs

{-@ measure sumsize @-}
sumsize :: [[a]] -> Int
sumsize [] = 0
sumsize (x:xs) = size x + sumsize xs

{-@ concat :: x:[[a]] -> {v:[a] | size v == sumsize x } @-}
concat :: [[a]] -> [a]
concat [] = []
concat (xs:[]) = xs
concat (xs:(ys:xss)) = concat ((append xs ys):xss)

{-@ append :: [a] -> [a] -> [a] @-}
append :: [a] -> [a] -> [a]
append xs [] = xs
append [] ys = ys
append (x:xs) ys = x:append xs ys