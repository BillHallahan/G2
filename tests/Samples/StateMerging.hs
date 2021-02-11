module Compress where

compress :: (Eq a) => [a] -> [a]
compress (x:(ys@(y:_)))
    | x == y = compress ys
    | otherwise = x : compress ys
compress ys = ys

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

any' :: [Bool] -> Bool
any' [] = False
any' (x:xs) = case x of
    True -> True
    False -> any' xs
        
sumIfAny :: [Bool] -> [Int] -> Int
sumIfAny a b = case (any' a) of
    True -> sum b
    False -> product b

data Buried a = Buried (Buried a) | Bottom a

dig :: Buried a -> a
dig (Bottom x) = x
dig (Buried x) = dig x
