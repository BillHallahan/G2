module Peano where

data Peano = Zero | Succ Peano

add Zero b = b
add (Succ a) b = Succ (add a b)

data HugeArgs = Go Int Int Int Int

fourth (Go _ _ _ a) = a

hue = let x = [1..]
      in head x

test :: Int -> Int -> Int -> Int
test a b c = if (a + b < c)
                 then a + b
                 else if (c < 5)
                     then b + c
                     else a + c

