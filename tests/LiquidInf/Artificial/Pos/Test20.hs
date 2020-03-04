{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

module Test20 () where

data D a = Emp | R a

{-@ measure size :: D a -> Int
    size (Emp) = 0
    size (R x) = 1
  @-}

{-@ invariant {v:D a | 0 <= size v} @-}

{-@ f :: D (Int, Int) -> (Int, {v:(D Int) | size v > 0}) @-}
f :: D (Int, Int) -> (Int, (D Int))
f xs = g xs

g :: D (Int, Int) -> (Int, (D Int))
g _ = (1, R 1)