module Main where

import Nat

f :: Int -> Int
f x = x

g :: Int -> Int
g x = x

one :: Int -> Int
one x = 1


{-# RULES
"fg" forall x . f x = g x
"f_one" forall x . f x = one x
"fg_toint" forall x . f (toInt x) = g (toInt x)
  #-}

main :: IO ()
main = putStrLn "Hello, Haskell!"
