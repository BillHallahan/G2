module Main where

import Helper
import MyLib

main :: IO ()
main = putStrLn "Hello, Haskell!"

f :: MyInt -> Int -> Int
f (MyInt x) y = call (MyInt y) + helper x + 1
f (MyIntAlso x) y = call (MyIntAlso y) + x + x + 1