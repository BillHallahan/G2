module Defunc4 where

data X = X

xToInt :: X -> Int
xToInt _ = 0

xToInt1 :: X -> Int
xToInt1 _ = 1

f :: (X -> Int) -> X -> Int
f g x = g x + g x

f2 :: (X -> Int) -> X -> Int
f2 g x = g x

data Z = Z (X -> Int)

f3 :: Z -> X -> Int
f3 (Z g) x = g x

same :: Z -> X -> Bool
same (Z g) x = g x /= g x

data ZZ = ZZ (X -> Z)

xToZ :: X -> Z
xToZ _ = Z xToInt

compZZ :: ZZ -> Bool
compZZ (ZZ f) =
    let
        (Z g) = f X
        (Z g') = f X
    in
    g X /= g' X

xToBool :: X -> Bool
xToBool _ = True

inlines :: (X -> Bool) -> Bool
inlines g = if toBool g then g X else False

toBool :: (X -> Bool) -> Bool
toBool f = f X

newtype Dollars = Dollars Int

mowLawn :: Dollars -> Dollars
mowLawn (Dollars d) = Dollars (d + 10)

makeMoney :: (Dollars -> Dollars) -> Dollars -> Dollars
makeMoney w d = w d
