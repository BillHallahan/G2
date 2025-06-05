module HigherOrder1 where

import G2.Symbolic

f :: (Int -> Int) -> Int -> Int
f h x = h (assert (x >= 0) 1)

g :: (Int -> Bool) -> Int -> Int
g h x = assert (h x) 1

data AB = A | B

higher :: ((AB -> AB) -> AB) -> Int
higher h =
    case h (\_ -> A) of
        A -> case h (\_ -> B) of
                B -> 1
                _ -> 2
        _ -> 3

c :: Int -> Int
c x = x

call :: (Int -> Int) -> Int -> Int
call h x = h (c x)
