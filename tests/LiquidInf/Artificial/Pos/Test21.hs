-- cmd_line = (--no-keep_quals)

{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

-- {-@ LIQUID "--maxparams=0"  @-}
-- {-@ LIQUID "--eliminate=all" @-}

module Test21 () where

{-@ f :: (Int, {x: Int | x > 0}) @-}
f :: (Int, Int)
f = g 1

g :: k -> (k, Int)
g k = (k, 1)