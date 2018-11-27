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

n1Map :: (Int -> Int) -> N1 -> N1
n1Map f (N1 i) = N1 (f i)

data X = X
newtype NewX = N X

f :: NewX -> X
f (N x) = x

g :: X -> NewX
g x = N x

h :: NewX
h = N X

newtype W a = W a

addW :: W Int -> W Int
addW (W x) = W x

mapW :: (a -> a) -> W a -> W a
mapW f (W x) = W (f x)

mapWInt :: (Int -> Int) -> W Int -> W Int
mapWInt = mapW

mapWAdd1Int :: W Int -> W Int
mapWAdd1Int = mapW add1

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

appLeft :: (Int -> Int) -> EInt a -> EInt a
appLeft f (EInt (L x)) = EInt (L (f x))
appLeft _ x = x

appLeftFloat :: (Int -> Int) -> EInt Float -> EInt Float
appLeftFloat f x = appLeft f x

add1 :: Int -> Int
add1 x = x + 1

sub1 :: Int -> Int
sub1 x = x - 1

data T a b c = TL a | TC b | TR c
newtype TFloat a b = TFloat (T a Float b)

getC :: TFloat a b -> Float
getC (TFloat (TC x)) = x
getC _ = error "not TC"

getTR :: TFloat a b -> b
getTR (TFloat (TR x)) = x
getTR _ = error "not TC"

getCIntFloatDouble :: TFloat Int Double -> Float
getCIntFloatDouble x = getC x

getRIntFloatDouble :: TFloat Int Double -> Double
getRIntFloatDouble x = getTR x

-- Note: TFloat' flips a and b
newtype TFloat' a b = TFloat' (T b Float a)

getTR' :: TFloat' a b -> a
getTR' (TFloat' (TR x)) = x
getTR' _ = error "not TC"

getRIntFloatX' :: TFloat' Int X -> Int
getRIntFloatX' x = getTR' x
