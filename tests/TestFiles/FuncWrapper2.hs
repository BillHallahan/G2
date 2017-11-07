-- This is to test the Higher Order Function Wrappers created in CreateFuncs.hs.
-- If we assume the function given to f satisfies fWrapper, and we assume fAssume, asserting fAssert on
-- f should generate no couterexamples.
-- But fAssume and fAssert alone should generate a counterexample, because of addNeg1.

module FuncWrapper2 where

fWrapper :: Int -> Int -> Bool
fWrapper x y = x < y

add1 :: Int -> Int
add1 = (+) 1

addNeg1 :: Int -> Int
addNeg1 = (+) (-1)

fAssume :: (Int -> Int) -> Int -> Int -> Bool
fAssume _ x _ = 0 < x

fAssert :: (Int -> Int) -> Int -> Int -> Bool
fAssert _ = (<)

f :: (Int -> Int) -> Int -> Int
f g x = g x + g x