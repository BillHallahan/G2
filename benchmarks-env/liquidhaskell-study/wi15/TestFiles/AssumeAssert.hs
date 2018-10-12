module AssumeAssert where

assertGt5 :: Int -> Int -> Bool
assertGt5 _ x = x > 5

assumeGt5 :: Int -> Int -> Bool
assumeGt5 _ x = x > 5

outShouldBeGt5 :: Int -> Int
outShouldBeGt5 x = let x' = if x < 0 then -x else x in x' + 6

outShouldBeGe5 :: Int -> Int
outShouldBeGe5 x = let x' = if x < 0 then -x else x in x' + 5

