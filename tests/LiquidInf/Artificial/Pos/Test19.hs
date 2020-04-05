{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

module Combined () where

data Assocs k a = Assocs [(k, a)]

{-@ f :: { x:Int | 0 <= x} -> Assocs {v:Int | 0 <= v } Int @-}
f :: Int -> Assocs Int Int
f x = g h

g :: (Int -> Assocs Int Int -> Assocs Int Int) -> Assocs Int Int
g op = h 1 (Assocs [])

h :: Int -> Assocs Int Int -> Assocs Int Int
h k (Assocs m) = Assocs ((1, 1):m)
