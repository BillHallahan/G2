module HigherOrderPre where

{-@ test :: (x:{ x:Int | x < 0 } -> Int) -> Int @-}
test :: (Int -> Int) -> Int
test f = f 10

{-@ g :: Int -> Int @-}
g :: Int -> Int
g x = x