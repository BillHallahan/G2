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

just :: Int -> Maybe Int
just n = Just n

{-# RULES
"addOneCommutative" forall n . addOne n = 1 + n
"doubleNegative" forall n . negation (negation n) = n
  #-}

{-# RULES
"maybeForceZero" forall x . maybeForce (Just x) = if x == x then maybeForce Nothing else x
"badNegation" forall a . negation a = negation $ negation a
  #-}

{-# RULES
"maxWithSelf" forall x y . maxOfInt x y = if x == y then y else x
"addOneJust" forall n . just (addOne n) = Just (1 + n)
  #-}