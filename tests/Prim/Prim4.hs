module Prim4 where

divIntTest :: Int -> Bool
divIntTest x 
    | x > 0 = (div x 2) > 1
    | x < 0 = (div x 2) > 0
    | x == 0 = (div x 2) > 2

divIntegerTest :: Integer -> Bool
divIntegerTest x = (div x 2) > 1

divIntegerTest2 :: Integer -> Bool
divIntegerTest2 x 
    | x > 0 = (div x 2) > 1
    | x < 0 = (div x 2) > 0
    | x == 0 = (div x 2) > 2

divFloatTest :: Float -> Bool
divFloatTest x = (x / 2) > 1