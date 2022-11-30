-- cmd_line = (--no-keep-quals)

{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

module Combined () where

import qualified Data.Map as M

data M a = Emp
         | C a
         deriving (Eq, Ord, Show)

{-@ measure size      :: M a -> Int
    size (Emp) = 0
    size (C x) = 1
  @-}

{-@ invariant {v:M a | 0 <= size v} @-}
{-@ invariant {v:M a | size v <= 1} @-}

f :: Int
f = g x

{-@ g  :: {xs:M (M Int) | size xs == 1} -> Int @-}
g :: M (M Int) -> Int
g _ = 0

x    :: M (M Int)
x = C (C 0)
