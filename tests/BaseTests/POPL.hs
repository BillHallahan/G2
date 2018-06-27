{-# LANGUAGE BangPatterns #-}

module POPL where

import Prelude hiding (zipWith, filter, head, zip, foldr, take, sum, (!!))


-- 1) Basic Symbolic Execution
zip :: [a] -> [b] -> [(a, b)]
zip [] _ = []
zip _ [] = []
zip (x:xs) (y:ys) = (x, y) : zip xs ys

-- 2) Lazy evaluation

inGe0 :: Int -> Int -> Bool
inGe0 x _ = x >= 0

is4Mod6 :: Int -> Int -> Bool
is4Mod6 _ r = r `mod` 6 == 4 

ith4Mod6 :: Int -> Int
ith4Mod6 i = kModNs 4 6 !! i

-- Supposed to return a list of numbers that are k mod n
kModNs :: Int -> Int -> [Int]
kModNs k n = k:kModNs (k + n) k

(!!)                    :: [a] -> Int -> a
xs     !! n | n < 0 =  error "Prelude.!!: negative index"
[]     !! _         =  error "Prelude.!!: index too large"
(x:_)  !! 0         =  x
(_:xs) !! n         =  xs !! (n-1)

takeNFromN :: Int -> [Int]
takeNFromN n = take n (range n)

inEven :: Int -> Int -> Bool
inEven x _ = x `mod` 2 == 0

outEven :: Int -> Int -> Bool
outEven _ x = x `mod` 2 == 0

sumKNats :: Int -> Int
sumKNats n = sum (take n (range 1))

sumKNats0 :: Int -> Int
sumKNats0 n = sum $ take n (range 0)-- [0..]

range :: Int -> [Int]
range x = x:range (x + 1) 

gt5 :: Int -> Int -> Bool
gt5 _ y = y > 5

sum :: [Int] -> Int
sum (x:xs) = x + sum xs
sum [] = 0

take                   :: Int -> [a] -> [a]
take n _      | n <= 0 =  []
take _ []              =  []
take n (x:xs)          =  x : take (n-1) xs

-- 3) Higher Order Func
succ :: Int -> Int
succ x = x + 1

abs :: Int -> Int
abs x
    | x > 0 = x
    | otherwise = -x

fixed :: (Int -> Int) -> Int -> Bool
fixed f x = x == (f x)






-- UNUSED:





-- 1) Lazy evaluation, 

takeFib :: Int -> [Int]
takeFib n = take n fibs

fibs :: [Int]
fibs = 0 : 1 : zipWith (+) fibs (tail fibs)

zipWith :: (a -> b -> c) -> [a] -> [b] -> [c]
zipWith f = go
  where
    go [] _ = []
    go _ [] = []
    go (x:xs) (y:ys) = f x y : go xs ys

-- 1)
fstCollatz :: ([Int] -> Bool) -> [Int]
fstCollatz p = head . filter p $ map collatz infEven

null :: [Int] -> Bool
null [] = True
null _ = False

lengthGt5 :: [Int] -> Bool
lengthGt5 xs = length xs > 5

infEven :: [Int]
infEven = infC 0 2

infC :: Int -> Int -> [Int]
infC x n = x:infC (x + n) n 

head :: [a] -> a
head (x:xs) = x
head _ = error "Bad head"

filter :: (a -> Bool) -> [a] -> [a]
filter _pred []    = []
filter pred (x:xs)
  | pred x         = x : filter pred xs
  | otherwise      = filter pred xs

collatz :: Int -> [Int]
collatz 1 = [1]
collatz x =
    if x `mod` 2 == 0
        then x:(collatz $ x `quot` 2)
        else x:(collatz $ 3 * x + 1)


isOdd :: Int -> Bool
isOdd x = x `mod` 2 == 1

