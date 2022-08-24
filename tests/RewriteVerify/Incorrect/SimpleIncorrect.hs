module SimpleIncorrect where

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

idTuple :: (Int, Int) -> (Int, Int)
idTuple x = x

data A = A | B

f :: A -> A -> A
f x y =
	case x of
		A -> case y of
				A -> A
				_ -> B
		_ -> case y of
				A -> B
				B -> B

{-# RULES
"badMaybeForce" forall x . maybeForce (Just x) = if x == x then maybeForce Nothing else x
"badNegation" forall a . negation a = negation $ negation a
"badMax" forall x y . maxOfInt x y = if x == y then y else x
"badMaxLeft" forall x y . maxOfInt x y = x
"badJust" forall n . just n = Nothing
"badTuple" forall n . idTuple n = (0, 0)

"badFF" forall x y . f x y = f y x

  #-}
