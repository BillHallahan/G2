-- As of Z3 4.5.0, and CVC4 1.5, Z3 can find 2 paths for the below function,
-- but CVC4 fails on 1 path, with an unknown
module CheckSq where

checkSq :: Int -> Int
checkSq x = case x * x of
                9 -> 0
                y -> y
