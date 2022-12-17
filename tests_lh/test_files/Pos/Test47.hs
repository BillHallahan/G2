--Simpler: Test46

module Test47 (f) where

{-@ f :: x:{ x:Int | x > 0 } -> Int @-}
f :: Int -> Int
f x = h g x

{-@ g :: Int -> Int -> Int -> Int @-}
g :: Int -> Int -> Int -> Int
g r _ _ | r <= 0 = die ""
g _ x y = x + y

h :: (a -> a -> a -> a) -> a -> a
h func x = func x x x 

{-@ die :: s:{ s:String | false } -> a @-}
die :: String -> a
die = error