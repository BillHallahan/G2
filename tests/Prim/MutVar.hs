{-# LANGUAGE MagicHash, UnboxedTuples #-}

module MutVar where

import GHC.Prim

f :: Int -> (Int, Int)
f x =
    let
        (# s1, mv #) = newMutVar# x realWorld#
        (# s2, x' #) = readMutVar# mv s1
    in
    case x' > 0 of
        True -> (x, x' + 1)
        False -> case x < 0 of
                    True -> (x, x')
                    False -> case x == 0 of
                                True -> (x, x' + 7)
                                False -> (x, x' - 8)

g :: Int -> (String, Int, Int)
g x =
    let
        (# s1, mv #) = newMutVar# 1 realWorld#
        s2 = writeMutVar# mv x s1
        (# s3, x' #) = readMutVar# mv s2
    in
    case compare x x' of
        LT -> ("LT", x, x')
        EQ -> ("EQ", x, x')
        GT -> ("GT", x, x')

h :: Int -> Int -> (Int, Int, Int)
h x y =
    let
        (# s1, mv1 #) = newMutVar# x realWorld#
        (# s2, mv2 #) = newMutVar# 5 s1
        (# s3, mv3 #) = newMutVar# y s2

        (# s4, rx #) = readMutVar# mv1 s3
        (# s5, ry #) = readMutVar# mv3 s4

        s6 = writeMutVar# mv3 x s5
        s7 = writeMutVar# mv1 y s6

        (# s8, e1 #) = readMutVar# mv1 s7
        (# s9, e2 #) = readMutVar# mv2 s8
        (# s10, e3 #) = readMutVar# mv3 s9
    in
    (e1, e2, e3)

i :: Int -> Int
i x =
    let
        (# s1, mv #) = newMutVar# x realWorld#
        s2 = writeMutVar# mv 6 realWorld#
        (# s3, x' #) = readMutVar# mv s1
    in
    x'

j :: Int -> Int
j x =
    let
        (# s1, mv #) = newMutVar# x realWorld#
        (# s3, x' #) = readMutVar# mv s1
        s2 = writeMutVar# mv 6 realWorld#
    in
    x'