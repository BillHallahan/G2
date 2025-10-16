module List4 where

import Prelude hiding (Num (..), zip)

zip [] _ = []
zip _ [] = []
zip (x:xs) (y:ys) = (x, y) : (zip xs ys)

zipConcat :: a -> [a] -> [b] -> [(a, b)]
zipConcat _ _ [] = []
zipConcat x xs (y:ys) = (x, y) : zip xs ys

p1 x xs ys = zip (x:xs) ys == zipConcat x xs ys

data Nat = S Nat | Z
  deriving (Show,Ord)

instance Eq Nat where
  Z == Z = True
  S p1 == S p2 = p1 == p2
  _ == _ = False

Z     + y = y
(S x) + y = S (x + y)

data AB = A | B

instance Eq AB where
    A == A = True
    B == B = True
    _ == _ = False

count :: AB -> [AB] -> Nat
count x [] = Z
count x (y:ys) =
  case x == y of
    True -> S (count x ys)
    _ -> count x ys

p2 n xs = count n xs == count n (xs ++ [])
