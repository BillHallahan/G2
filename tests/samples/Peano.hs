module Peano where

data Peano = Succ Peano | Zero

add :: Peano -> Peano -> Peano
add Zero p = p
add (Succ p) p2 = add p (Succ p2)

multiply :: Peano -> Peano -> Peano
multiply _ Zero = Zero
multiply p (Succ p2) = add p (multiply p p2)

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

eqEachOtherAndAddTo4 :: Peano -> Peano -> Peano -> Bool
eqEachOtherAndAddTo4 p p2 p3 = toInt p == toInt p2 && toInt p3 == 4