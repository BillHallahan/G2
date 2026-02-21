module HigherOrder where

prop1 :: () -> () -> (() -> () -> Int) -> Bool
prop1 x y g = g x y == g y x