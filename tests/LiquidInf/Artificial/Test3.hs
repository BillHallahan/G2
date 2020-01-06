{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

module Combined  where

import Prelude hiding (length, replicate, foldr, foldr1, map, concat, zipWith, repeat)

import qualified Data.Map as M

import Data.List (minimumBy)

data List a = Emp
            | C a
              deriving (Eq, Ord, Show)

{-@ measure size      :: List a -> Int
    size (Emp) = 0
    size (C x) = 1
  @-}

{-@ invariant {v:List a | 0 <= size v} @-}

f :: Int
f = g x

{-@ g  :: List {xs:(List Int) | size xs > 0} -> Int @-}
g :: List (List Int) -> Int
g _ = 0

{-@ x :: List { xs:(List Int) | size xs /= -1 } @-}
x    :: List (List Int)
x = Emp
