module HigherOrder2 (c) where

{-@ c :: x:Int -> { y:Int | y > x } @-}
c :: Int -> Int
c = f g

{-@ f :: (Int -> Int) -> x:Int -> { y:Int | y > x } @-}
f :: (Int -> Int) -> Int -> Int
f h i = h i

{-@ g :: Int -> Int @-}
g :: Int -> Int
g x = x + 1