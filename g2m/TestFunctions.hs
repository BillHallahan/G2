module TestFunctions where

import Data.Maybe

compress :: (Eq a) => [a] -> [a]
compress (x:(ys@(y:_)))
    | x == y = compress ys
    | otherwise = x : compress ys
compress ys = ys

compressTest :: (Eq a) => [a] -> [a] -> Bool
compressTest xs ys = compress xs == ys

compressTest2 :: (Eq a) => Int -> [a] -> [a] -> Bool
compressTest2 a xs ys = (compress xs == compress ys) && (length ys > (length xs + a))

filter' :: (a -> Bool) -> [a] -> [a]
filter' pred [] = []
filter' pred (x:xs)
    | pred x = x : filter' pred xs
    | otherwise = filter' pred xs

sumEvens :: [Int] -> Int
sumEvens = sum . filter' (\a -> a `mod` 2 == 0)

sumEvensTestFixed :: [Int] -> Bool
sumEvensTestFixed xs = length xs > 4 * 2 && sumEvens xs == 4 * 2

-- Improvement from 390s to 16s when merging enabled, with x = 5
sumEvensTest :: [Int] -> Int -> Bool
sumEvensTest xs x =  sumEvens xs == 2 && length xs > x * 2

any' :: [Bool] -> Bool
any' [] = False
any' (x:xs) = case x of
    True -> True
    False -> any' xs
        
sumIfAny :: [Bool] -> [Int] -> Int
sumIfAny a b = case (any' a) of
    True -> sum b
    False -> product b

isSubsequenceOf' :: (Eq a) => [a] -> [a] -> Bool
isSubsequenceOf' [] _ = True
isSubsequenceOf' _ [] = False
isSubsequenceOf' a@(x:a') (y:b)
    | x == y    = isSubsequenceOf' a' b
    | otherwise = isSubsequenceOf' a b

-- Improvement from 7s to 0.59s with merging, for a = [1,2,1,3]
subseqOfTest :: [Int] -> [Int] -> Bool
subseqOfTest a b = (isSubsequenceOf' a b) && (length b > 8)

foldrSimple :: (a -> b -> b) -> b -> [a] -> b
foldrSimple f z [] = z
foldrSimple f z (x:xs) = f x (foldrSimple f z xs)

keepJust :: Maybe Int -> Int -> Int
keepJust a b = case a of
    Just x -> (b + 1)
    Nothing -> b

-- Improvement from 7.4s to 5.6s with merging enabled
foldrTest :: Int -> [Maybe Int] -> Bool
foldrTest z xs = ((foldrSimple keepJust z xs) > 3) && (length xs > 7)

-- Improvement from 22s to 3s with merging enabled
foldrTest2 :: Int -> [Maybe Int] -> [Maybe Int] -> Bool
foldrTest2 z xs ys = ((foldrSimple keepJust z xs) + (foldrSimple keepJust z ys)) > 9

data Tree = Nil | Node (Tree) Int (Tree)

treeInsert :: Tree -> Int -> Tree
treeInsert Nil x = Node Nil x Nil
treeInsert (Node t1 y t2) x
    | y == x = Node t1 y t2
    | y < x = Node t1 y (treeInsert t2 x)
    | otherwise = Node (treeInsert t1 x) y t2

treeSize :: Tree -> Int
treeSize t = case t of
    Nil -> 0
    Node t1 x t2 -> (treeSize t1) + 1 + (treeSize t2)

treeSizeTest :: Int -> Tree -> Bool
treeSizeTest i t = (treeSize (treeInsert t i)) > (treeSize t)

sieve :: [Int] -> [Int]
sieve (p : xs) = p : sieve [x | x <- xs, x `mod` p /= 0]
sieve [] = []

-- Slow for both
sieveTest :: Int -> [Int] -> Bool
sieveTest a b = (length (sieve b)) > a

divide :: Int -> Int -> Int -> Int
divide num divisor quotient =
    let rem = num - divisor
    in if rem > 0
        then divide rem divisor (quotient + 1)
        else quotient

-- Improvement from 36s to 8s with merging enabled
divideTest :: Int -> Int -> Int -> Int -> Bool
divideTest numA numB divisorA divisorB =
    let quotA = (divide numA divisorA 0)
        quotB = (divide numB divisorB 0)
    in (quotA == quotB) && (numA /= numB) && (quotA > 20) && (numA > 0) && (numB > 0)


