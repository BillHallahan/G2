module SimpleCorrect where

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

t2 :: Int -> Int
t2 = (* 2)

nop :: a -> a
nop a = a

{-# RULES
"addOneCommutative" forall n . addOne n = 1 + n
"doubleNegative" forall n . negation (negation n) = n
"maybeForceZero" maybeForce Nothing = 0
"maxWithSelf" forall x . maxOfInt x x = x
"addOneJust" forall n . just (addOne n) = Just (1 + n)
"justJust" forall n . just n = Just n
"plusDouble" forall n . t2 n = n + n
"polymorphism" forall x . nop x = x
"doublePlusOne" forall n . addOne (t2 n) = 1 + n + n
  #-}
