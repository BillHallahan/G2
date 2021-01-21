module SimpleRules where

addOne :: Int -> Int
addOne n = n + 1

negation :: Int -> Int
negation n = -n

{-# RULES
  "addOne commutative" forall n . addOne n = 1 + n
  "negation idempotent" forall n . negation (negation n) = n
  #-}