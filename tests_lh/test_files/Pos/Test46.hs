module Test46 (f) where

{-@ f :: x:{ x:Int | x > 0 } -> Int @-}
f :: Int -> Int
f x = h g x

{-@ g :: Int -> Int @-}
g :: Int -> Int
g x = x + x

h :: (a -> a) -> a -> a
h func x = func x
