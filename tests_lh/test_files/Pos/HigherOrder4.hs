module HigherOrder4 (c) where

{-@ c :: x:{x:Int | x > 0 } -> Int @-}
c :: Int -> Int
c = f g

{-@ f :: (Int -> Int) -> Int -> Int @-}
f :: (Int -> Int) -> Int -> Int
f h i = h i

{-@ g :: Int -> Int @-}
g :: Int -> Int
g 0  = error "g called with 0"
g x = x + 1