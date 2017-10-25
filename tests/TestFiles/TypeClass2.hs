module TypeClass2 where

class Test a where
    test :: a -> a

    bar :: a

instance Test Int where
    test x = x

    bar = 0

f :: Int -> Int
f x = test x