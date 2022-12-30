module Nat where

data Nat = Z | Succ Nat

add :: Nat -> Nat -> Nat
add Z y = y
add (Succ x) y = Succ (add x y)

toInt :: Nat -> Int
toInt Z = 0
toInt (Succ x) = 1 + toInt x

{-# RULES
"add_assoc" forall x y z . add x (add y z) = add (add x y) z
  #-}

