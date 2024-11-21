module Peano where

data Peano = Succ Peano | Zero deriving (Show, Eq)

add :: Peano -> Peano -> Peano
add Zero p = p
add (Succ p) p2 = add p (Succ p2)

add2 :: Peano -> Peano -> Peano
add2 Zero p = p
add2 (Succ p) p2 = Succ (add p p2)

--Subtracts the smaller number from the larger number
sub :: Peano -> Peano -> Peano
sub (Succ p1) (Succ p2) = sub p1 p2
sub p1 Zero = p1
sub Zero p2 = p2 

multiply :: Peano -> Peano -> Peano
multiply _ Zero = Zero
multiply p (Succ p2) = add p (multiply p p2)

isEven :: Peano -> Bool
isEven (Succ (Succ p1)) = isEven p1
isEven Zero = True
isEven _ = False

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

equalsTwo :: Peano -> Peano -> Peano -> Bool
equalsTwo _ _ p = toInt p == 2

eq :: Peano -> Bool
eq p = toInt (add p p) == 4

isTrue ::Peano -> Bool -> Bool
isTrue _ b = b

eqEachOtherAndAddTo4 :: Peano -> Peano -> Peano -> Bool
eqEachOtherAndAddTo4 p p2 p3 = toInt p == toInt p2 && toInt p3 == 4

multiplyToFour :: Peano -> Peano -> Peano -> Bool
multiplyToFour p1 p2 _ = toInt (multiply p1 p2) == 4

fstIsEvenAddToFour :: Peano -> Peano -> Peano -> Bool
fstIsEvenAddToFour p1 _ p3 = (isEven p1) && (toInt p3 == 4)

fstIsTwo :: Peano -> Peano -> Peano -> Bool
fstIsTwo p1 _ _ = toInt p1 == 2
