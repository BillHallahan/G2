module NumOrd where

{-@ sub :: Num a => {x:a | x > 0} -> {y:a | y >= 0} @-}
sub :: Num a => a -> a 
sub x = x - 1

{-@ subF :: {x:Float | x > 0} -> {y:Float | y >= 0} @-}
subF :: Float -> Float 
subF x = x - 1


{-@ f :: Num a => {x:a | x > 0} -> {y:a | y >= x} @-}
f :: Num a => a -> a 
f x = x

{-
{-@ f' :: Ord a => {x:a | x > 0} -> {y:a | y >= x} @-}
f' :: Ord a => a -> a 
f' x = x
-}

data AB = A | B deriving Show

instance Eq AB where
	x == y = False


{-@ neq :: x:AB -> y:AB -> { b:Bool | b <=> (x /= y) } @-}
neq :: AB -> AB -> Bool
neq A A = False
neq B B = False
neq _ _ = True

instance Num AB where
	A + x = x
	x + A = x
	B + B = A

	A * _ = A
	_ * A = A
	B * B = B

	abs x = x

	signum _ = B

	fromInteger x = if x `mod` 2 == 0 then A else B

	negate x = x

{-@ test :: Num a => {x:a | x > 0} -> {y:a | y > x} -> Bool @-}
test :: Num a => a -> a -> Bool
test _ _ = True

testApp1 :: Bool
testApp1 = test A B

testApp2 :: Bool
testApp2 = test A B