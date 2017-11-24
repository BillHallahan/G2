module Peano where

data Peano = Succ Peano | Zero

{-@ add :: x:Peano -> y:Peano -> {z:Peano | toInt x < toInt z && toInt y < toInt z} @-}
add :: Peano -> Peano -> Peano
add Zero p = p
add (Succ p) p2 = add p (Succ p2)

{-@ measure toInt @-}
toInt :: Peano -> Int
toInt Zero = 0
toInt (Succ p) = 1 + toInt p
