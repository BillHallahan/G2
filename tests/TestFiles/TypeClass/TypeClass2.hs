module TypeClass2 where

class Test a where
    test :: a -> a

    bar :: a

instance Test Int where
    test x = x

    bar = 0

instance Test Float where
    test x = x + 1
    bar = 1

f :: Int -> Int
f x = test x

g :: Float -> Float
g x = test x