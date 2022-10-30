module Unevaluated where

f :: Int -> Int
f x = g [x]

{-@ g :: [{x:Int | x > 0}] -> Int @-}
g :: [Int] -> Int
g _ = 0
