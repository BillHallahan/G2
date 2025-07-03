module Nat where

import Prelude hiding ((+),(*),(-),(<),id)
--import Tip

data Nat = Z | S Nat deriving (Eq,Ord)

infix 3 ===
infix 3 =/=
infixr 0 ==>

-- Added this function

given :: Bool -> Bool -> Bool
given pb pa = (not pb) || pa

(===) :: Eq a => a -> a -> Bool
(===) = (==)

(==>) :: Bool -> Bool -> Bool
(==>) = given

x =/= y = not (x === y)

infixl 6 -
infixl 6 +
infixl 7 *

(+) :: Nat -> Nat -> Nat
S n + m = S (n + m)
Z   + m = m

(*) :: Nat -> Nat -> Nat
S n * m = m + (n * m)
Z   * m = Z

-- | Truncated subtraction
(-) :: Nat -> Nat -> Nat
S n - S m = n - m
S m - Z   = S m
Z   - Z   = Z
Z   - _   = Z

(<) :: Nat -> Nat -> Bool
Z{} < Z   = False
Z < _     = True
S{} < Z   = False
S n < S m = n < m

(=:=) :: Nat -> Nat -> Bool
Z   =:= Z   = True
Z{} =:= S{} = False
S{} =:= Z{} = False
S n =:= S m = n =:= m

plus_idem x = x + x === x
plus_not_idem x = x + x === x ==> True === False
plus_inf x =  S x === x
plus_ninf x =  S x === x ==> True === False

mul_idem  x = x * x === x

silly x y z = x * (y + z) === (x * y) + z

sub_assoc x y z = x - (y - z) === (x - y) - z

not_trans x y z = x < y === True ==> y < z === True ==> x < z === False

sub_comm  x y   = x - y === y - x
