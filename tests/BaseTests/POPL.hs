module POPL where

import Prelude hiding (zipWith, filter, head, zip, foldr)


-- 1) Basic Symbolic Execution
zip :: [a] -> [b] -> [(a, b)]
zip [] _ = []
zip _ [] = []
zip (x:xs) (y:ys) = (x, y) : zip xs ys

-- 2) Lazy evaluation
sumKNats :: Int -> Int
sumKNats n = foldr (+) 0 $ take n inf 

foldr            :: (a -> b -> b) -> b -> [a] -> b
foldr _ z []     =  z
foldr f z (x:xs) =  f x (foldr f z xs)



inf :: [Int]
inf = inf' 0

inf' :: Int -> [Int]
inf' x = x:inf' (x + 1) 

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

isEven :: Int -> Bool
isEven x = x `mod` 2 == 0

isOdd :: Int -> Bool
isOdd x = x `mod` 2 == 1

