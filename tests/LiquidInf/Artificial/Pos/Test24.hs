-- cmd_line = (--no-keep-quals)

{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

module ListQualif ( List ) where

import Prelude hiding (map)

data List = Emp
          | R Double
          deriving (Eq, Ord, Show)

{-@ measure size :: List -> Int
    size (Emp) = 0
    size (R x) = 1
  @-}

{-@ invariant {v:List | 0 <= size v} @-}

{-@ type ListN N = {v:List | size v = N} @-}

{-@ f :: x:Double -> { r:Double | r == x } @-}
f :: Double -> Double
f = g

g :: Double -> Double
g x = x / 1