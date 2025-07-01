module Peano where

import Prelude
  ( Eq
  , Ord
  , Show
  , Int
  , Bool(..)
  , (==)
  )

import qualified Prelude as P

Z     + y = y
(S x) + y = S (x + y)

Z     - _     = Z
x     - Z     = x
(S x) - (S y) = x - y

(=:=) :: Eq a => a -> a -> Bool
(=:=) = (==)

data Nat = S Nat | Z

instance Eq Nat where
  Z == Z = True
  S p1 == S p2 = p1 == p2
  _ == _ = False

_     < Z     = False
Z     < _     = True
(S x) < (S y) = x < y

intToNat :: Int -> Nat
intToNat 0 = Z
intToNat n = S (intToNat (n P.- 1))

-- True properties
p1 n = (n - n =:= Z)

p2 n m = (n - (n + m) =:= Z)

p3 n = (n - n =:= h n)

h n = if n == S n then S Z else Z

p4 n = S n < S (S n)

p5 :: (Int -> Bool) -> Int -> Bool
p5 f n = f n == f n

p6 n m = ((n + m) - n =:= m)


-- False properties
p1False n = (n - n =:= if n == S (S Z) then S Z else Z)

p2False n = (n - n =:= if n == intToNat (100 P.* 100) then S Z else Z)

p3False n = n < n

p5False :: (Int -> Bool) -> Int -> Bool
p5False f n = f n
