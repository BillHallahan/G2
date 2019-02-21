{-@ LIQUID "--prune-unsorted" @-}

module Concat where

import Prelude hiding (concat)

-- Example from Section 2.5 in the paper.
-- The refinement on concat has an error, discoverable by calling G2.
-- Suggestion: pass '--cut-off 100' on the command line to speed up execution (this is particularly a problem in the VM)

{-@ measure size @-}
size :: [a] -> Int
size [] = 0
size (_:xs) = 1 + size xs

{-@ measure sumsize @-}
sumsize :: [[a]] -> Int
sumsize [] = 0
sumsize (x:xs) = size x + sumsize xs

{-@ concat :: x:[[a]] -> {v:[a] | size v = sumsize x} @-}
concat :: [[a]] -> [a]
concat [] = []
concat (xs:[]) = xs
concat (xs:(ys:xss)) = concat ((append xs ys):xss)

append :: [a] -> [a] -> [a]
append xs [] = xs
append [] ys = ys
append (x:xs) ys = x:append xs ys
