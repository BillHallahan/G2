module List5 where

import Prelude hiding (Num (..), (++), last, not, null, zip)

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

not :: Bool -> Bool
not True = False
not False = True

(==>) :: Bool -> Bool -> Bool
pb ==> pa = (not pb) || pa

infixr 0 ==>

p1False n xs = n == n ==> S (count n xs) == count n [n]
