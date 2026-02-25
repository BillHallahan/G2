module List6 where

import Prelude hiding ((+))

data Nat = S Nat | Z
  deriving (Show,Ord)

instance Eq Nat where
  Z == Z = True
  S p1 == S p2 = p1 == p2
  _ == _ = False

Z     + y = y
(S x) + y = S (x + y)

count :: Nat -> [Nat] -> Nat
count x [] = Z
count x (y:ys) =
  case x == y of
    True -> S (count x ys)
    _ -> count x ys

p1False :: Nat -> Nat -> [Nat] -> Bool
p1False n x xs
  = (count n [x] + count n xs == count n (x:x:xs))
