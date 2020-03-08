-- cmd_line = (--no-keep_quals)

{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

module Combined () where

data D a = Emp
         | R a
         deriving (Eq, Ord, Show)

{-@ measure size :: D a -> Int
    size (Emp) = 0
    size (R x) = 1
  @-}

{-@ invariant {v:D a | 0 <= size v} @-}

{-@ f :: {v:Int | 1 <= v } @-}
f :: Int
f = g (R 0)

g :: (Ord k) => D k -> Int
g _ = 1