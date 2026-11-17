module List9 where

p1 :: [[Int]] -> Bool
p1 xs = myfoldr (<>) xs == myfoldr (<>) xs

myfoldr :: ([Int] -> [Int] -> [Int]) -> [[Int]] -> [Int]
myfoldr k = go
          where
            go []     = []
            go (y:ys) = y `k` go ys
