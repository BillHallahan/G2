module TypeClass1 where

class Test a where
    test :: a -> a

instance Test Int where
    test x = x

f :: Int -> Int
f x = test x

polySnd a b = b

typedSnd :: Int -> Int -> Int
typedSnd a b = b

