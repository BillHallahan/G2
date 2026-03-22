module HigherOrder where

prop1 :: () -> () -> (() -> () -> Int) -> Bool
prop1 x y g = g x y == g y x

prop2 :: (Int -> [Int]) -> Int -> Bool
prop2 f x = g f x == f x 

g :: (Int -> [Int]) -> Int -> [Int]
g h n = h n