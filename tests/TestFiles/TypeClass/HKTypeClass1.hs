module HKTypeClass1 where

class Extract m where
    extract :: m a -> a

    replace :: a -> m b -> m a

    change :: (a -> b) -> m a -> m b
    change f w =
        let
            x = extract w
        in
        replace (f x) w

data J a = J a

data E a b = E a b

instance Extract J where
    extract (J x) = x

    replace x _ = J x

instance Extract (E a) where
    extract (E _ x) = x

    replace y (E x _) = E x y

largeJ :: J Int -> Int -> Bool
largeJ _ x = x > 100

largeE :: E Int Int -> Int -> Bool
largeE _ x = x > 100

extractJ :: J Int -> Int
extractJ j = extract j

extractE :: E Int Int -> Int
extractE e = extract e

changeJ :: (Int -> Int) -> J Int -> J Int
changeJ f j = change f j

add1 :: Int -> Int
add1 x = x + 1

add2 :: Int -> Int
add2 x = x + 2