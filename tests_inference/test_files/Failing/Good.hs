{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

module Test where

{-@ f :: n:Int -> t1:(Int, { x:Int | x == n }) -> (Int, { y:Int | y == snd t1 }) -> (Int, { z:Int | z == n }) @-}
f :: Int -> (Int, Int) -> (Int, Int) -> (Int, Int)
f n (n1, p1) (n2, p2) = g (n1, p1) (n2, p2)

g :: a -> a -> a
g x y = y