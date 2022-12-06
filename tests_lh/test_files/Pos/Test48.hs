--Simpler: Test47

module Test48 (f) where

{-@ f :: x:{ x:Int | x > 0 } -> (Int, Int) @-}
f :: Int -> (Int, Int)
f x = h g (x, x)

{-@ g :: (Int, Int) -> (Int, Int) @-}
g :: (Int, Int) -> (Int, Int)
g (_, r) | r <= 0 = die ""
g (x, _) = (x, 1)

h :: (a -> a) -> a -> a
h func x = func x

{-@ die :: s:{ s:String | false } -> a @-}
die :: String -> a
die = error