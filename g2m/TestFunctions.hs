module TestFunctions where

compress :: (Eq a) => [a] -> [a]
compress (x:(ys@(y:_)))
    | x == y = compress ys
    | otherwise = x : compress ys
compress ys = ys

compressTest :: (Eq a) => [a] -> [a] -> Bool
compressTest xs ys = compress xs == ys

compressTest2 :: (Eq a) => [a] -> [a] -> Bool
compressTest2 xs ys = length xs > length ys + 4 && compress xs == ys

last' :: [a] -> a
last' [x] = x
last' (x:xs) = last' xs
last' [] = error "Empty list"

lastSums :: [Int] -> [Int] -> Int
lastSums a b = (last' a) + (last' b)

filter' :: (a -> Bool) -> [a] -> [a]
filter' pred [] = []
filter' pred (x:xs)
    | pred x = x : filter' pred xs
    | otherwise = filter' pred xs

sumEvens :: [Int] -> Int
sumEvens = sum . filter' (\a -> a `mod` 2 == 0)

sumEvensTestFixed :: [Int] -> Bool
sumEvensTestFixed xs = length xs > 4 * 2 && sumEvens xs == 4 * 2

sumEvensTest :: [Int] -> Int -> Bool
sumEvensTest xs x =  sumEvens xs == x - 1 && length xs > x * 2

any' :: [Bool] -> Bool
any' [] = False
any' (x:xs) = case x of
    True -> True
    False -> any' xs
        
sumIfAny :: [Bool] -> [Int] -> Int
sumIfAny a b = case (any' a) of
    True -> sum b
    False -> product b