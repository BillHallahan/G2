module TyApps where

data C a = C a

class Container t where
    contains :: t a -> a

instance Container C where
    contains (C x) = x

{-@ getPosInt :: Container t => t { x:Int | x >= 0 } -> { y:Int | y > 0 } @-}
getPosInt :: Container t => t Int -> Int
getPosInt = contains

{-@ getPos :: (Num a, Container t) => t { x:a | x >= 0 } -> { y:a | y > 0 } @-}
getPos :: (Num a, Container t) => t a -> a
getPos = contains