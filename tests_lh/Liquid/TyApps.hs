module TyApps where

data C a = C a deriving Eq

class Container t where
    contains :: t a -> a

instance Container C where
    contains (C x) = x

{-@ getLt10Int :: Container t => t { x:Int | x <= 10 } -> { y:Int | y < 10 } @-}
getLt10Int :: Container t => t Int -> Int
getLt10Int = contains

{-@ getLt10 :: (Num a, Container t) => t { x:a | x <= 10 } -> { y:a | y < 10 } @-}
getLt10 :: (Num a, Container t) => t a -> a
getLt10 = contains


{-@ goodGet :: (Num a, Container t) => t { x:a | x < 5 } -> { y:a | y < 10 } @-}
goodGet :: (Num a, Container t) => t a -> a
goodGet = contains
