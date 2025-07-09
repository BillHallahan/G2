{-# LANGUAGE BangPatterns #-}

module Infinite1 where

import Prelude ( Bool (..), Eq (..))

data Nat = S Nat | Z

instance Eq Nat where
  Z == Z = True
  S p1 == S p2 = p1 == p2
  _ == _ = False

Z     + y = y
(S x) + y = S (x + y)

Z     - _     = Z
x     - Z     = x
(S x) - (S y) = x - y

infNat :: Nat
infNat = S infNat

p1 :: Nat -> Nat -> Bool
p1 n m = (n - (n + infNat) == Z)

p1False :: Nat -> Nat -> Bool
p1False n m = ((n + infNat) - n == Z)
