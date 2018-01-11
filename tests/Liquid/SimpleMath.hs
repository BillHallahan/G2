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

-- {-@ subToPos :: x:Pos -> {y:Int | x >= y} -> Pos @-}
-- subToPos :: Int -> Int -> Int
-- subToPos x y = x - y

-- -- fib and fib' are from
-- -- https://ucsd-progsys.github.io/liquidhaskell-blog/2013/01/27/refinements101-reax.lhs/

-- -- This is also wrong because it does not check that n >= 0, but we can't
-- -- currently find counterexamples for this case...
-- {-@ fib :: n:Int -> { b:Int | (n >= 0 && b >= n) } @-}
-- fib :: Int -> Int
-- fib 0 = 0
-- fib 1 = 1
-- fib n = fib (n - 1) + fib (n - 2)

-- {-@ fib' :: n:{v:Int | v >= 0} -> {b:Int | (n >= 0 && b >= n) } @-}
-- fib' :: Int -> Int
-- fib' 0 = 0
-- fib' 1 = 1
-- fib' n = fib' (n - 1) + fib' (n - 2)

id2Int :: Int -> Int
id2Int x = id2 x

{-@ id2 :: x:a -> {y:a |  y == x} @-}
id2 :: a -> a
id2 x = x

{-@ eq2 :: x:a -> y: a-> {b:Bool | b <=> x == y} @-}
eq2 :: Eq a => a -> a -> Bool
eq2 x y = x == y