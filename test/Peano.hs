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

equalsFour :: Peano -> Peano -> Peano -> Bool
equalsFour _ _ p = toInt p == 4

eq :: Peano -> Bool
eq p = toInt (add p p) == 4

isTrue ::Peano -> Bool -> Bool
isTrue _ b = b

equalsFive :: Peano -> Bool
equalsFive p = toInt p == 5