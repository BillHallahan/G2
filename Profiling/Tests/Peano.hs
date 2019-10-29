module Peano where

data Peano = Succ Peano | Zero deriving (Show, Eq)

-- Peano
-- Test 1: add assert "equalsFour" -- works, but is slower
-- Test 2: add, assert "equalsFour" assume "multiplyToFour" -- works, marginally slower
-- Test 3: add, assert "fstIsTwo" assume "fstIsEvenAddToFour" -- works, marginally slower
--
add :: Peano -> Peano -> Peano
add Zero p = p
add (Succ p) p2 = add p (Succ p2)

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

multipleFour :: Peano -> Bool
multipleFour (Succ (Succ (Succ (Succ p1)))) = multipleFour p1
multipleFour Zero = True
multipleFour _ = False

multipleOfFours :: Peano -> Peano -> Peano -> Bool
multipleOfFours p1 p2 _ = (not . multipleFour $ p1) && (not . multipleFour $ p2)

multipleFive :: Peano -> Peano -> Peano -> Bool
multipleFive p1 p2 (Succ (Succ (Succ (Succ (Succ p3))))) = True -- multipleFive p1 p2 p3
multipleFive _ _ Zero = True
multipleFive _ _ _ = False

addIfFiveOrTen :: Peano -> Peano -> Peano
addIfFiveOrTen p1 (Succ (Succ (Succ (Succ (Succ p2))))) = (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (add p1 p2)))))))))))
addIfFiveOrTen p1 p2 = (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (add p1 p2)))))))))))

addInts :: Int -> Int -> Peano
addInts x y = 
    let
        x' = fromInt x
        y' = fromInt y
    in
        add x' y'

addPeano :: Peano -> Peano -> Int
addPeano x y = 
    let
        x' = toInt x
        y' = toInt y
    in
        x' + y'

evenMutRecursive :: Peano -> Bool
evenMutRecursive Zero = True
evenMutRecursive (Succ p) = oddMutRecursive p

oddMutRecursive :: Peano -> Bool
oddMutRecursive Zero = False
oddMutRecursive (Succ p) = evenMutRecursive p
