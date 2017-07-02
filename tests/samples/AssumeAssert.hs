module AssumeAssert where

assertGt5 :: Int -> Bool
assertGt5 x = x > 5

assumeGt5 :: Int -> Bool
assumeGt5 x = x > 5

outShouldBeGt5 :: Int -> Int
outShouldBeGt5 x = let x' = if x < 0 then (-x) else x in x' + 6

outShouldBeGe5 :: Int -> Int
outShouldBeGe5 x = let x' = if x < 0 then (-x) else x in x' + 5

