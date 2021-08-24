module Sets1 (f) where

import Data.Set

{-@ f :: xs:Set Int -> ys:Set Int -> { zs:Set Int | zs = Set_cap xs ys } @-}
f :: Set Int -> Set Int -> Set Int
f = g

{-@ g :: s1:(Set Int) -> (Set Int) -> {r : (Set Int) | (Set_sub (Set_cup r s1) s1)}  @-}
g :: Set Int -> Set Int -> Set Int
g = intersection
