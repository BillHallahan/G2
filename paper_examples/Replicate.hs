{-@ LIQUID "--prune-unsorted" @-}

module Replicate where

import Prelude hiding (replicate)

-- Example from Section 6.2 in the paper.
-- Calling LH on the replicate function produces an interesting counterfactual counterexample,
-- due to replicate's non-termination

{-@ measure size @-}
size :: [a] -> Int
size [] = 0
size (_:xs) = 1 + size xs

{-@ replicate :: n:Int -> a -> { xs:[a] | size xs == n} @-}
replicate :: Int -> a -> [a]
replicate 0 x = []
replicate n x = x:replicate n x
