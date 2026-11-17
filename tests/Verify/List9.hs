module List9 where

p1 :: [[Int]] -> Bool
p1 xs = mcon xs == myfoldr (<>) xs

mcon :: [[Int]] -> [Int]
mcon [] = []
mcon (xs:xss) = xs ++ mcon xss

myfoldr :: ([Int] -> [Int] -> [Int]) -> [[Int]] -> [Int]
myfoldr k = go
          where
            go []     = []
            go (y:ys) = y `k` go ys
