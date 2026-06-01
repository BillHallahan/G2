module MyLib where

data MyInt = MyInt Int | MyIntAlso Int deriving Eq

call :: MyInt -> Int
call (MyInt x) = x * 2
call (MyIntAlso x) = x * 4

otherCall :: Int -> Int
otherCall x = x

{-# NOINLINE noinline #-}
noinline :: Int -> Int
noinline x = x * 17