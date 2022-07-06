module HigherOrder3 (c) where

{-@ c :: x:{ x:Int | x > 0 } -> y:{ y:Int | y > 0 } -> { z:Int | z > x && z > y } @-}
c :: Int -> Int -> Int
c = f g

{-@ f :: (Int -> Int -> Int) -> Int -> Int -> Int @-}
f :: (Int -> Int -> Int) -> Int -> Int -> Int
f h i j = h i j

{-@ g :: Int -> Int -> Int @-}
g :: Int -> Int -> Int
g x y = x + y + 1