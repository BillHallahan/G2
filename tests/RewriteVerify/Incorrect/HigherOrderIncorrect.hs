module HigherOrderIncorrect where

import Data.List

int :: Int -> Int
int x = x

{-# RULES
"direct" forall (f :: Int -> Int) (g :: Int -> Int) . int (f (g 1)) = int (f 1)
  #-}

data Nat = Z
         | S Nat
         deriving (Show, Eq)

lmap :: (a -> b) -> [a] -> [b]
lmap _ [] = []
lmap f (h:t) = (f h) : (lmap f t)

-- tests relating to polymorphic functions and variables
-- the output should be SAT for all three of these rewrite rules
infNat1 :: Nat
infNat1 = S infNat1

infNat2 :: Nat
infNat2 = S infNat2

apply :: (a -> b) -> a -> b
apply f x = f x

{-# RULES
"symFuncInfExpr" forall p . lmap p [infNat1] = lmap p [infNat2]
"symFuncPoly" forall p . apply p (S Z) = apply p Z
"symFuncNat" forall (p :: Nat -> Nat) . apply p (S Z) = apply p Z
  #-}
