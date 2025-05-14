module IfTest where

f :: Int -> Int -> Int
f a b =
    if a == b then
        a + b
    else
        b

g :: Int -> Int -> Int -> Int
g a b c =
    if a < b then
        (if c > b then a + b else 
            (if a + 17 == c then c + a else a + b + c))
    else
        b
