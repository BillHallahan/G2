module SimpleMath where

{-@ type Pos = {v:Int | 0 < v} @-}
{-@ type PosDouble = {v:Double | 0.0 < v} @-}

{-@ abs2 :: x:Double -> PosDouble @-}
abs2 :: Double -> Double
abs2 x
    | x > 0 = x
    | otherwise = -x

{-@ add :: x:Int -> y:Int -> {z:Int | x <= z && y <= z}@-}
add :: Int -> Int -> Int
add x y = x + y

{-@ subToPos :: x:Pos -> {y:Int | x >= y} -> Pos @-}
subToPos :: Int -> Int -> Int
subToPos x y = x - y

-- fib and fib' are from
-- https://ucsd-progsys.github.io/liquidhaskell-blog/2013/01/27/refinements101-reax.lhs/

-- This is also wrong because it does not check that n >= 0, but we can't
-- currently find counterexamples for this case...
{-@ fib :: n:Int -> { b:Int | (n >= 0 && b >= n) } @-}
fib :: Int -> Int
fib 0 = 0
fib 1 = 1
fib n = fibx (n - 1) + fibx (n - 2)

fibx :: Int -> Int
fibx 0 = 0
fibx 1 = 1
fibx n = fibx (n - 1) + fibx (n - 2)

{-@ fib' :: n:{v:Int | v >= 0} -> {b:Int | (n >= 0 && b >= n) } @-}
fib' :: Int -> Int
fib' 0 = 0
fib' 1 = 1
fib' n = fib2' (n - 1) + fib2' (n - 2)

fib2' :: Int -> Int
fib2' 0 = 0
fib2' 1 = 1
fib2' n = fib2' (n - 1) + fib2' (n - 2)

{-@ xSqPlusYSq :: x:Int -> y:Int -> {z:Int | x + y < z} @-}
xSqPlusYSq :: Int -> Int -> Int
xSqPlusYSq x y = x * x + y * y

{-@ id2Int :: x:Int -> {y:Int | y /= x} @-}
id2Int :: Int -> Int
id2Int x = x

{-@ id2 :: x:a -> {y:a | y /= x} @-}
id2 :: a -> a
id2 x = x

{-@ eq2 :: x:a -> y: a-> {b:Bool | b <=> x == y} @-}
eq2 :: Eq a => a -> a -> Bool
eq2 x y = x == y

{-@ eq3Int :: x:Int -> y:Int -> {b:Bool | x == y} @-}
eq3Int :: Int -> Int -> Bool
eq3Int x y = x == y


{-@ eq3 :: x:a -> y:a -> {b:Bool | x == y} @-}
eq3 :: Eq a => a -> a -> Bool
eq3 x y = x == y

{-@ add2 :: x:Int -> y:Int -> {z:Int | x < z }@-}
add2 :: Int -> Int -> Int
add2 x y = x + y

{-@ add3 :: x:Double -> y:Double -> {z:Double | x < z }@-}
add3 :: Double -> Double -> Double
add3 x y = x + y

{-@ add4 :: x:Int -> y:Int -> {z:Int | x <= z }@-}
add4 :: Int -> Int -> Int
add4 x y = x + y

{-@ add5 :: x:Int -> y:Int -> {z:Int | x > z }@-}
add5 :: Int -> Int -> Int
add5 x y = x + y

{-@ add6 :: x:Int -> y:Int -> {z:Int | x >= z }@-}
add6 :: Int -> Int -> Int
add6 x y = x + y

{-@ lt :: {b:Bool | 1 < 0} @-}
lt :: Bool
lt = False

{-@ neg :: Int -> {y:Int | 0 < y} @-}
neg :: Int -> Int
neg x = -x
