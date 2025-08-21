module Defunc1 where

data A = A (Int -> Int)
       | B Int

f :: A -> A
f (A g) = B (case g 2 of 0 -> -1; y -> y)
f x = x

h :: (Int -> Int) -> Int
h fg = fg 0

add1 :: Int -> Int
add1 x = x + 1

multiply2 :: Int -> Int
multiply2 x = x * 2

data X = X (Int -> Int)

x :: X -> Int
x (X g) = g 4

newtype Dollars = Dollars Int deriving Eq

deskJob :: Dollars -> Dollars
deskJob (Dollars d) = Dollars (d + 100)

mowLawn :: Dollars -> Dollars
mowLawn (Dollars d) = Dollars (d + 10)

makeMoney :: (Dollars -> Dollars) -> Dollars -> Dollars
makeMoney w d = w d

newtype Y a = Y a deriving Eq

mapY :: (a -> a) -> Y a -> Y a
mapY f (Y x) = Y (f x)

yAdd1 :: Y Int -> Y Int
yAdd1 (Y x) = Y (x + 1)

mapYInt :: (Y Int -> Y Int) -> Y Int -> Y Int
mapYInt f x = f x 

data Z = Z (Int -> Int)

data ZZ = ZZ (Int -> Z)

genZ :: Int -> Z
genZ x = Z (const x)

genZ2 :: Int -> Z
genZ2 x = Z (const (- x))

-- Should always be false
compZApps :: Z -> Int -> Bool
compZApps (Z f) x = f x /= f x

compZApps2 :: Z -> Int -> Bool
compZApps2 z x =
    let
        r1 = helper z x
        r2 = helper z x
    in
    r1 /= r2

{-# NOINLINE helper #-}
helper :: Z -> Int -> Int
helper (Z f) x = f x

compZZ :: ZZ -> Int -> Int -> Bool
compZZ (ZZ f) x y =
    let
        (Z g) = f x
        (Z g') = f x
    in
    g y /= g' y

compZZ2 :: ZZ -> Int -> Int -> Bool
compZZ2 zz@(ZZ g) x y =
    let
        (Z f) = zzHelper zz x
        (Z f') = g x
    in
    f y /= f' y

{-# NOINLINE zzHelper #-}
zzHelper :: ZZ -> Int -> Z
zzHelper (ZZ f) x = f x

data E = E | EE deriving Eq

data T = T (E -> E)

data TT = TT (E -> T)

e :: E -> E
e E = EE
e EE = E

genT :: E -> T
genT x = T (const x)

compTT2 :: TT -> E -> E -> Bool
compTT2 tt@(TT g) x y =
    let
        (T f) = case tt of
                    TT g' -> g' x
        (T f') = g x
    in
    f y /= f' y
