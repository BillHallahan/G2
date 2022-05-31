{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

module Test where

{-@ f :: n:Nat -> (Int, {x:Int | x == n}) -> (Int, {x:Int | x == n}) @-}
f :: Int -> (Int, Int) -> (Int, Int)
f n ps = call (g n) ps

call :: (a -> a -> a) -> a -> a
call op x = op x x

{-@ g :: n:Int -> t1:(Int, { x:Int | x == n }) -> (Int, { y:Int | y == snd t1 }) -> (Int, { z:Int | z == n }) @-}
g :: Int -> (Int, Int) -> (Int, Int) -> (Int, Int)
g n (n1, p1) (n2, p2) = (n1, p1)