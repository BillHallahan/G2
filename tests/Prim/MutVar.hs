{-# LANGUAGE MagicHash, UnboxedTuples #-}

module MutVar where

import GHC.Prim

f :: Int -> (Int, Int)
f x =
    let
        (# s1, mv #) = newMutVar# x realWorld#
    in
    fIn mv x

fIn :: MutVar# RealWorld Int -> Int -> (Int, Int)
fIn mv x =
    let
        (# s2, x' #) = readMutVar# mv realWorld#
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

-- k1 can yield two outputs:
--     (2, 6) if different MutVars are passed for mv1 and mv2
--     (6, 6) if the same MutVar is passed as mv1 and mv2
-- Contrastingly, k2 will yield only the output (2, 6), because the MutVar mv1 that is passed in
-- cannot be the same as the MutVar mv2 that is created via newMutVar# in k2.
k1 :: MutVar# RealWorld Int -> MutVar# RealWorld Int -> (Int, Int)
k1 mv1 mv2 =
    let
        s1 = writeMutVar# mv1 2 realWorld#
        s2 = writeMutVar# mv2 6 s1
 
        (# s3, x1 #) = readMutVar# mv1 s2
        (# s4, x2 #) = readMutVar# mv2 s3 
    in
    (x1, x2)

k2 :: MutVar# RealWorld Int -> (Int, Int)
k2 mv1 =
    let
        (# s1, mv2 #) = newMutVar# 99 realWorld#
    in
    k1 mv1 mv2
