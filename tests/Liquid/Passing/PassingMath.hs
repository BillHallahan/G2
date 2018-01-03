module PassingMath where

{-@ add :: x:Int -> y:Int -> {z:Int | x + y == z}@-}
add :: Int -> Int -> Int
add x y = x + y

{-@ lt :: x:Int -> y:Int -> {z:Int | x < z}@-}
lt :: Int -> Int -> Int
lt x y = x + 1

-- {-@ addPoly :: x:a -> {y:a | x + y == x} -> {z:a | x + y == z} @-}
-- addPoly :: a -> a -> a
-- addPoly x y = x

{-@ ltPoly :: x:a -> {y:a | x < y} -> {z:a | x < z} @-}
ltPoly :: a -> a -> a
ltPoly _ y = y

data Test = X | Y | Z deriving Eq

instance Ord Test where
	X <= Y = True
	Z <= X = True
	_ <= _ = False

	X < Y = True
	Z < X = True
	Z < Y = False
	Y < Z = False
	_ < _ = False


{-@ ltTest :: x:Test -> {y:Test | x < y} -> {z:Test | x < z} @-}
ltTest :: Test -> Test -> Test
ltTest _ y = y

{-@ ltTest2 :: x:Test -> {y:Test | x < y} -> {z:Test | x < z || y <= z} @-}
ltTest2 :: Test -> Test -> Test
ltTest2 x y = if x < y then y else x

-- ltTest2 Y Z violates refinement type 
-- (by the typeclass def- it holds for a well founded ordering)