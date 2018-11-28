module Prim2 where

-- Integral
quotI1 :: Int -> Int -> Bool
quotI1 x y = x `quot` y == 7

quotI2 :: Int -> Int -> Bool
quotI2 x y = x `quot` y == -7

remI1 :: Int -> Int -> Bool
remI1 x y = x `rem` y == 7

remI2 :: Int -> Int -> Bool
remI2 x y = x `rem` y == -7

--Various combinations
p1 :: Int -> Int
p1 x =
    let
        y = (6 * (39 `quot` x) + 3 + x) `quot` 9
        z = x * x * 10
    in
    y + z

p2 :: Int -> Int -> (Bool, Bool)
p2 x y =
    let
        a = x + y > x * y
        b = -x `quot` (-y) == x `rem` y
    in
    (a || b, a && b)

p1List :: [Int]
p1List = [p1 x | x <- [1..300]]

p2List :: [(Bool, Bool)]
p2List = [p2 x y | x <- [1..15], y <- [1..40]]

integerToFloatList :: [Float]
integerToFloatList = [ fromInteger x | x <- [1..500] :: [Integer]]

sqrtList :: [Float]
sqrtList = [ x + 1 | x <- [1.0..150.0] :: [Float]]

sqrtList2 :: [Float]
sqrtList2 = [ x | x <- [1.0..1.0] :: [Float]]
