module SimpleRules where

addOne :: Int -> Int
addOne n = n + 1

negation :: Int -> Int
negation n = -n

{-# RULES
"addOneCommutative" forall n . addOne n = 1 + n
"doubleNegative" forall n . negation (negation n) = n
  #-}