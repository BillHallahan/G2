{-# LANGUAGE MultiWayIf #-}

module Approx1 where

filterCall1 :: [Int] -> [Int]
filterCall1 = filter isEven
    where
        isEven x = x `mod` 2 == 0 

filterCall2 :: [Int] -> (Int, [Int])
filterCall2 xs =
    case filter isGt0 xs of
        [] -> (1, [])
        ys -> (2, ys)
    where
        isGt0 x = x > 0

filterCall3 :: [Int] -> (Int, [Int])
filterCall3 xs =
    case filter isEven xs of
        [] -> (1, [])
        ys -> (2, ys)
    where
        isEven x = x `mod` 2 == 0 

lengthCall1 :: [Int] -> Int -> Int
lengthCall1 xs y | y >= myLength xs = 1
lengthCall1 xs y = 2

myLength :: [Int] -> Int
myLength [] = 0
myLength (_:xs) = 1 + myLength xs

indexCall1 :: [Int] -> Int -> Int
indexCall1 xs y = xs !! y
