module TypeClass1 where

class Test a where
    test :: a -> a

instance Test Int where
    test x = x

f :: Int -> Int
f x = test x

polySnd a b = b

typedSnd :: Int -> Int -> Int
typedSnd a b = polySnd a b

polyMax :: (Ord a) => a -> a -> a
polyMax a b = if a > b then a else b

typedMax :: Int -> Int -> Int
typedMax a b = polyMax a b

