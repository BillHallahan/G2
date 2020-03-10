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

{-@ f :: ListN 1 -> ListN 1 @-}
f :: List -> List
f = appG

appG :: List -> List
appG Emp = Emp
appG (R x) = R (x / 1)