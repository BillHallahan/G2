{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

module TestFunctions where

import Data.Maybe
import Data.Data
import G2.QuasiQuotes.G2Rep

compress :: (Eq a) => [a] -> [a]
compress (x:(ys@(y:_)))
    | x == y = compress ys
    | otherwise = x : compress ys
compress ys = ys

compressTest :: (Eq a) => [a] -> [a] -> Bool
compressTest xs ys = (compress xs == ys)

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

$(derivingG2Rep ''Tree)

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

mccarthy :: Int -> Int
mccarthy x
    | x > 100 = x - 10
    | otherwise = mccarthy (mccarthy (x + 11))

greaterThan10Less :: Int -> Int -> Bool
greaterThan10Less x y = z > 150 && y == z - 10
    where z = mccarthy x

greaterThanNot10Less :: Int -> Int -> Bool
greaterThanNot10Less x y = z > 100 && y /= z - 10
    where z = mccarthy x

-- | improvement from 15s to <1s with state merging enabled
validateLuhn :: Int -> [Int] -> Bool
validateLuhn a idn = validLength && val `mod` 10 == 0
   where 
    validLength = length idn  > a
    val = sum $ zipWith doubleEven [0..] (reverse idn)
    doubleEven :: Int -> Int -> Int
    doubleEven n x | n `mod` 2 == 1 = let dbl = 2*x in if (dbl > 9) then dbl - 9 else dbl
                   | otherwise = x

-- | Slower with state merging enabled. Able to find xs that satisfies predicate quickly with SM enabled when using G2 executable
runLengthEncodeTest :: (Eq a) => Int -> [a] -> Bool
runLengthEncodeTest a xs = (length $ runLengthEncode xs) + a < (length xs)

runLengthEncode :: (Eq a) => [a] -> [(Int, a)]
runLengthEncode [] = []
runLengthEncode (x:xs) = (length $ x : takeWhile (==x) xs, x) : runLengthEncode (dropWhile (==x) xs)

-- | Slightly slower with state merging enabled. 1s -> 13s with len = 15
reverseTest :: Int -> [Int] -> Bool
reverseTest len a = ((reverse' a) == a) && (length a > len)

reverse' :: (Eq a) => [a] -> [a]
reverse' list = reverse'' list []
    where
       reverse'' [] reversed     = reversed
       reverse'' (x:xs) reversed = reverse'' xs (x:reversed)

range' :: Int -> Int -> [Int]
range' lo hi
    | lo <= hi = lo : range' (lo + 1) hi
    | otherwise = []

-- | Much slower with state merging enabled
rangeAssert :: Int -> Int -> Bool
rangeAssert lo hi = (length res) == ((hi-lo) + 1) && (hi >= 0) && (lo >= 0) && (hi - lo > 5)
    where res = range' lo hi

get :: [a] -> Int -> a
get xs j = case xs of
            h:t -> case j == 0 of
                True -> h
                False -> get t (j - 1)

repl :: Int -> [Int]
repl x = x:repl (x+1)

-- | Slightly faster with state merging enabled. 29s -> 11s
replGetTest :: Int -> Int -> Int -> Bool
replGetTest i j k = (get (repl i) k) + (get (repl j) k) > 80 && i < 4 && j < 6

type Vector a = [a]

vectorAdd :: (Eq a, Num a) => [a] -> [a] -> [a]
vectorAdd (x:xs) (y:ys) = (x+y):(vectorAdd xs ys) 
vectorAdd (x:xs) [] = (x:xs)
vectorAdd [] (y:ys) = (y:ys)
vectorAdd [] [] = []

-- | Marginally slower with state merging enabled for large res (0.2s -> 0.4s for length res == 13)
vectorAddTest :: (Eq a, Num a) => [a] -> [a] -> [a] -> Bool
vectorAddTest a b res = (vectorAdd a b) == res

data Peano = Succ Peano | Zero deriving (Show, Eq)

$(derivingG2Rep ''Peano)

add :: Peano -> Peano -> Peano
add Zero p = p
add (Succ p) p2 = add p (Succ p2)

isEven :: Peano -> Bool
isEven (Succ (Succ p1)) = isEven p1
isEven Zero = True
isEven _ = False

toInt :: Peano -> Int
toInt Zero = 0
toInt (Succ p) = 1 + toInt p

fstIsEvenAddToFour :: Peano -> Peano -> Bool
fstIsEvenAddToFour p1 p2 = (isEven p1) && ((toInt (add p1 p2)) == 4)
