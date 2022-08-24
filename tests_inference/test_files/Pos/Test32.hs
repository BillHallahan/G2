module Combined (f) where

{-@ f :: {x:Int | 0 <= x && x <= 2 } -> ({ x:Int | 0 <= x && x <= 3 }, { x:Int | -17 <= x && x <= 0 }) @-}
f :: Int -> (Int, Int)
f x = (g x, h x)

g :: Int -> Int
g x
    | x == 1 = 3
    | otherwise = x

h :: Int -> Int
h x
    | x == 0 = -2
    | otherwise = m x

m :: Int -> Int
m = n

n :: Int -> Int
n x
    | x == 1 = -3
    | x == 2 = -17
    | otherwise = die "n"

{-@ die :: {v:String | false} -> a @-}
die str = error ("Oops, I died!" ++ str)
