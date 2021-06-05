module MeasComp where

{-@ f :: x:Int -> { y:Int | x == y } @-}
f :: Int -> Int
f x = g (0, x)

{-@ g :: (Int, Int) -> Int @-}
g :: (Int, Int) -> Int
g (_, x) = x