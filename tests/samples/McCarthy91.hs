module McCarthy91 where

mccarthy :: Int -> Int
mccarthy x
    | x > 100 = x - 10
    | otherwise = mccarthy (mccarthy (x + 11))

lessThan91 :: Int -> Int -> Bool
lessThan91 x y = x <= 100 && y == 91

lessThanNot91 :: Int -> Int -> Bool
lessThanNot91 x y = x <= 100 && y /= 91

greaterThan10Less :: Int -> Int -> Bool
greaterThan10Less x y = x > 100 && y == x - 10

greaterThanNot10Less :: Int -> Int -> Bool
greaterThanNot10Less x y = x > 100 && y /= x - 10