module TypeClass1 where

class Test a where
    test :: a -> a -> a

    bar :: a -> a -> a -> a

instance Test Int where
    test x y = x + y

    bar x y z = x + y + z

instance Test [a] where
    test s1 s2 = s1 ++ s2

    bar s1 s2 s3 = s1 ++ s3 ++ s2

f :: Int -> Int
f x = test x (bar 1 2 x)


