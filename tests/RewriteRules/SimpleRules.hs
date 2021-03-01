module SimpleRules where

addOne :: Int -> Int
addOne n = n + 1

negation :: Int -> Int
negation n = -n

maybeForce :: Maybe Int -> Int
maybeForce (Just n) = n
maybeForce Nothing = 0

maxOfInt :: Int -> Int -> Int
maxOfInt x y = if x < y then y else x

{-# RULES
"addOneCommutative" forall n . addOne n = 1 + n
"doubleNegative" forall n . negation (negation n) = n
  #-}

{-# RULES
"maybeForceZero" forall x . maybeForce (Just x) = maybeForce Nothing
"badNegation" forall a . negation a = negation $ negation a
  #-}

{-# RULES
"maxWithSelf" forall x y . maxOfInt x y = x
  #-}