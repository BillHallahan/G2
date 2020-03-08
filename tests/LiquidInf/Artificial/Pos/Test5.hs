-- cmd_line = (--no-keep_quals)

{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

module Combined () where

import qualified Data.Map as M

data D a = Emp
         | R a
         deriving (Eq, Ord, Show)

{-@ measure size :: D a -> Int
    size (Emp) = 0
    size (R _) = 1
  @-}

{-@ invariant {v:D a | 0 <= size v} @-}

{-@ f :: D (D Int) -> Nat @-}
f :: D (D Int) -> Int
f xs = g xs

g :: D a -> Int
g xs = 1