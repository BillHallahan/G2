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

just :: t -> Maybe t
just n = Just n

-- TODO remove this file, not needed anymore

{-

{-# RULES
"addOneCommutative" forall n . addOne n = 1 + n
"doubleNegative" forall n . negation (negation n) = n
  #-}

{-# RULES
"badMaybeForce" forall x . maybeForce (Just x) = if x == x then maybeForce Nothing else x
"badNegation" forall a . negation a = negation $ negation a
"badMax" forall x y . maxOfInt x y = if x == y then y else x
"badMaxLeft" forall x y . maxOfInt x y = x
  #-}

{-# RULES
"maybeForceZero" maybeForce Nothing = 0
"maxWithSelf" forall x . maxOfInt x x = x
"addOneJust" forall n . just (addOne n) = Just (1 + n)
"justJust" forall n . just n = Just n
  #-}

-}