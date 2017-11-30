module HKTypeClass1 where

class Extract m where
    extract :: m a -> a

data J a = J a

data E a b = E a b

instance Extract J where
    extract (J x) = x

instance Extract (E a) where
    extract (E _ x) = x

largeJ :: J Int -> Int -> Bool
largeJ _ x = x > 100

largeE :: E Int Int -> Int -> Bool
largeE _ x = x > 100

extractJ :: J Int -> Int
extractJ j = extract j

extractE :: E Int Int -> Int
extractE e = extract e