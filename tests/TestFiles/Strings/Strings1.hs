module Strings1 where

con :: String -> String -> String
con xs ys = xs ++ ys

eq :: String -> String -> Bool
eq xs ys = xs == ys

eqGt1 :: String -> String -> Bool
eqGt1 xs ys = xs == ys && length xs >= 1

capABC :: String -> String
capABC ('a':xs) = 'A':capABC xs
capABC ('b':xs) = 'B':capABC xs
capABC ('c':xs) = 'C':capABC xs
capABC (x:xs) = x:capABC xs
capABC "" = ""

appendEq :: String -> String
appendEq s = s ++ "!"

exclaimEq :: String -> String -> Bool
exclaimEq s1 s2 = s1 == s2 ++ "!"