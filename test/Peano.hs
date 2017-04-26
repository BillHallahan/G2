module Peano where

data Peano = Succ Peano | Zero

add :: Peano -> Peano -> Peano
add Zero p = p
add (Succ p) p' = add p (Succ p')

multiply :: Peano -> Peano -> Peano
multiply _ Zero = Zero
multiply p (Succ p') = add p (multiply p p')

toInt :: Peano -> Int
toInt Zero = 0
toInt (Succ p) = 1 + toInt p

fromInt :: Int -> Peano
fromInt x
    | x == 0 = Zero
    | x > 0 = Succ (fromInt (x - 1))
    | otherwise = Zero

equalsFour :: Peano -> Bool
equalsFour p = toInt p == 2

equalsFive :: Peano -> Bool
equalsFive p = toInt p == 5