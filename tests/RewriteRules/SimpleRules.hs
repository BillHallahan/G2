module SimpleRules where

addOne :: Int -> Int
addOne n = n + 1

negation :: Int -> Int
negation n = -n

maybeForce :: Maybe Int -> Int
maybeForce (Just n) = n
maybeForce Nothing = 0

{-# RULES
"addOneCommutative" forall n . addOne n = 1 + n
"doubleNegative" forall n . negation (negation n) = n
  #-}

{-# RULES
"maybeForceZero" forall k . maybeForce (Just 0) = maybeForce Nothing
"badNegation" forall a b . negation a = negation b
  #-}