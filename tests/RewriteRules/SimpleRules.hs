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
"maybeForceZero" maybeForce (Just 0) = maybeForce Nothing
"badNegation" forall a . negation a = negation $ negation a
  #-}