module Sets1 (f) where

import Data.Set

{-@ f :: xs:Set Int -> ys:Set Int -> { zs:Set Int | zs = Set_cap xs ys } @-}
f :: Set Int -> Set Int -> Set Int
f = g

{-@ g :: Set Int -> Set Int -> Set Int @-}
g :: Set Int -> Set Int -> Set Int
g = intersection
