{-# LANGUAGE MultiParamTypeClasses #-}

module MultiParamTypeClasses1 where

class F2 x y where
    v2 :: x -> y

instance F2 Int Int where
    v2 x | x > 0 = x
         | otherwise = -x

instance F2 Char Int where
    v2 'a' = 101
    v2 'b' = 102
    v2 'c' = 103
    v2  _  = 104

total :: Int -> Char -> Int
total x c = v2 x + v2 c

totalGen :: F2 a b => a -> b
totalGen = v2

totalGenNum :: (F2 a b, Num b) => a -> b
totalGenNum x = v2 x + v2 x

class F3 x y z where
    v3 :: x -> y -> z

instance F3 Int Int Int where
    v3 x y | x > 0 = x + y
           | otherwise = x - y

instance F3 Char Char Int where
    v3 'a' 'a' = 101
    v3 'b' 'b' = 102
    v3 'c' 'c' = 103
    v3  _ _ = 104

total3 :: Int -> Int -> Char -> Char -> Int
total3 x y c1 c2 = v3 x y + v3 c1 c2

totalGen3 :: F3 a b c => a -> b -> c
totalGen3 = v3

totalGenNum3 :: (F3 a b c, Num c) => a -> b -> c
totalGenNum3 x y = v3 x y + v3 x y

class G x y where
    g :: x -> y

instance G Char Char where
    g 'a' = 'b'
    g 'b' = 'c'
    g 'c' = 'd'
    g  _  = 'e'

instance G Float Float where
    g x | x > 10 = x + 1
    g _ = 1

testG :: G x y => x -> y
testG = g