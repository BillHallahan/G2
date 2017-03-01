module Peano where

data Peano = Zero | Succ Peano

add Zero b = b
add (Succ a) b = Succ (add a b)

pue :: Int -> Int
pue 123 = 0
pue a   = a

eqtest a = if a == 3 then 2 else 5

