module NewType1 where

newtype N1 = N1 Int
newtype N2 = N2 N1
newtype N3 = N3 N2
newtype N4 = N4 N3

add1N4 :: N4 -> N4
add1N4 (N4 n3) = N4 (add1N3 n3)

add1N3 :: N3 -> N3
add1N3 (N3 n2) = N3 (add1N2 n2)

add1N2 :: N2 -> N2
add1N2 (N2 n1) = N2 (add1N1 n1)

add1N1 :: N1 -> N1
add1N1 (N1 x) = N1 (x + 1)

data X = X
newtype NewX = N X

f :: NewX -> X
f (N x) = x

g :: X -> NewX
g x = N x

h :: NewX
h = N X

data E a b = L a | R b
newtype EInt a = EInt (E Int a)

getL :: EInt a -> Int
getL (EInt (L x)) = x
getL _ = error "not L"

getLIntFloat :: EInt Float -> Int
getLIntFloat e = getL e

getR :: EInt a -> a 
getR (EInt (R x)) = x
getR _ = error "not R"

getRIntFloat :: EInt Float -> Float
getRIntFloat e = getR e

data T a b c = TL a | TC b | TR c
newtype TInt a b = TInt (T Int a b)

getC :: TInt a b -> a 
getC (TInt (TC x)) = x
getC _ = error "not TC"

getCIntFloatDouble :: TInt Float Double -> Float
getCIntFloatDouble x = getC x