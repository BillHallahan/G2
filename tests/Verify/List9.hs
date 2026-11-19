module List9 where

data A = A

instance Eq A where
    _ == _ = True

p1 :: [[A]] -> Bool
p1 xs = myfoldr (<>) xs == myfoldr (<>) xs

myfoldr :: ([A] -> [A] -> [A]) -> [[A]] -> [A]
myfoldr k = go
          where
            go []     = []
            go (y:ys) = y `k` go ys
