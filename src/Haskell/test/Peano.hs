module Peano where

data Peano = Zero | Succ Peano

add Zero b = b
add (Succ a) b = Succ (add a b)

a :: Int -> Int
a 0 = 0
a n = let k = b 1
      in k + 2

b :: Int -> Int
b 0 = 1
b n = let f = a 1
      in f + 1

hue = let x = [1..]
      in head x

