{-# LANGUAGE BangPatterns, MultiWayIf #-}

module ListTests where

-- import qualified Data.Map as M
import Data.List

test :: Int -> Int
test x = x

maxMap :: Int -> Int
maxMap a = maximum (map (+1) [1, 2, a, 4, 5])

minTest :: Int -> Int
minTest a = minimum [1, 2, 3, a]

initsTest :: [Int] -> [[Int]]
initsTest xs = inits xs

foldrTest :: Int -> Int
foldrTest a = foldr (+) 0 [1, a, 3]

foldrTest2 :: Int -> Int
foldrTest2 a = foldr (+) 4 [1, a, 3, 4, 5]

hd :: [Int] -> Int
hd xs = head xs

hdTail :: [Int] -> Int
hdTail xs = head $ tail xs

-- g2Entry6 :: Int -> Int
-- g2Entry6 a = let m = M.fromList [(1, 'a'), (2, 'b')]
--                  m' = M.insert a 'c' m
--              in case M.lookup 1 m' of
--                Just _ -> 13579
--                _ -> 24680

fromListIntFloat :: [(Int, Float)] -> [(Int, Float)]
fromListIntFloat = foldr (:) []

fromListInt :: [Int] -> [Int]
fromListInt = foldr (:) []

foldrx :: (a -> b -> b) -> b -> [a] -> b
foldrx k z = go
          where
            go []     = z
            go (y:ys) = y `k` go ys

map2 :: [(a, b)] -> [b]
map2 xs =
    case map snd xs of
        _:_:ys -> ys
        _:ys -> ys
        [] -> []

filterCall1 :: [Int] -> (Int, [Int])
filterCall1 xs =
    case filter (\y -> y `mod` 2 == 0) xs of
        ys@(x:_) | x == 2 -> (1, ys)
                 | length ys < 2 -> (2, ys)
                 | length xs == length ys -> (3, ys)
                 | 2 `elem` ys -> (4, ys)
                 | any (< 10) ys -> (5, ys)
                 | otherwise -> (6, ys)
        [] -> (7, [])

nubCall1 :: [Int] -> (Int, [Int])
nubCall1 xs =
    case nub xs of
        [] -> (1, [])
        ys | length ys < 2 -> (2, ys)
           | length xs == length ys -> (3, ys)
           | otherwise -> (4, ys)  

indexCall1 :: [Int] -> Int -> (Int, Maybe Int)
indexCall1 xs y | 0 <= y && y < length xs =
    let x = xs !! y
        z = if | x < 100 -> 1
               | x > 200 -> 2
               | y < 2 -> 3
               | otherwise -> 4

    in
    (z, Just x)
indexCall1 _ y | 0 <= y = (5, Nothing)
               | otherwise = (6, Nothing)

indexCall2 :: [Int] -> Int -> (Int, Maybe Int)
indexCall2 xs y =
    let x = xs !! y
        z = if | x < 100 -> 1
               | x > 200 -> 2
               | y < 2 -> 3
               | otherwise -> 4

    in
    (z, Just x)

-- g2Entry7 :: Int -> [(Int, Int)]
-- g2Entry7 a = let m = M.fromList [(123456, a)]
--              in M.toList m

-- g2Entry8 :: [(Int, Float)] -> M.Map Int Float
-- g2Entry8 = M.fromList

lengthN :: [Int] -> Int
lengthN xs = length xs

lengthBranch :: [Int] -> Int
lengthBranch xs =
        let len = length xs in
        if | len > 5 -> 1
           | len > 2 -> 2
           | len == 0 -> 3
           | otherwise -> 4

fibonacci :: [Int]
fibonacci = let fibs = 0 : 1 : zipWith (+) fibs (tail fibs)  
            in fibs

testFib :: Int -> ([Int], Bool)
testFib n =
    let fib = take n fibonacci in
    case length fib of
        7 -> (fib, True)
        3 -> (fib, True)
        _ -> (fib, False)

unionTest :: Int -> [Int] -> [Int] -> ([Int], Int)
unionTest v xs ys | v `notElem` xs
                  , v `elem` ys = (xs `union` ys, 1)
                  | v `notElem` ys
                  , v `elem` xs = (xs `union` ys, 2)
                  | otherwise = (xs `union` ys, 3)