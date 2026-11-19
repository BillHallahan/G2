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

data Nat = S Nat | Z

(===) :: Nat -> Nat -> Bool
Z === Z = True
S p1 === S p2 = p1 === p2
_ === _ = False

count :: Nat -> [Nat] -> Nat
count x [] = Z
count x (y:ys) =
  case x === y of
    True -> S (count x ys)
    _ -> count x ys

p2 n xs = (S (count n xs) === count n (n : xs))
