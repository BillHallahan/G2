module Prim where

g :: Int -> Int
g 0 = 1
g _ = 2

f :: Int -> Int
f x = x + g x