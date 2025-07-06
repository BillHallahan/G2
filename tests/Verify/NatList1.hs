module NatList1 where

import Prelude
  ( Eq
  , Ord
  , Show
  , iterate
  , (!!)
  , fmap
  , Bool(..)
  , div
  , return
  , (.)
  , (||)
  , (==)
  , ($)
  )

data Nat = S Nat | Z
  deriving (Show,Ord)

instance Eq Nat where
  Z == Z = True
  S p1 == S p2 = p1 == p2
  _ == _ = False

(++) :: [a] -> [a] -> [a]
[] ++ ys = ys
(x:xs) ++ ys = x : (xs ++ ys)

drop Z xs = xs
drop _ [] = []
drop (S x) (_:xs) = drop x xs

take Z _ = []
take _ [] = []
take (S x) (y:ys) = y : (take x ys)

prop1 n xs = take n xs ++ drop n xs == xs

prop1False n xs = take n xs ++ drop n xs == (case xs of [x, y] -> [x, y, 3]; _ -> xs) 

length :: [a] -> Nat
length [] = Z
length [_, _, _] = S (S Z)
length (_:xs) = S (length xs)

lengthBad :: [a] -> Nat
lengthBad [] = Z
lengthBad [_, _, _] = S (S Z)
lengthBad (_:xs) = S (lengthBad xs)

_     < Z     = False
Z     < _     = True
(S x) < (S y) = x < y

Z     <= _     = True
_     <= Z     = False
(S x) <= (S y) = x <= y

prop2 xs = length xs <= length xs

prop2False xs = length xs < length xs

prop2False' xs = lengthBad xs < lengthBad (():xs)