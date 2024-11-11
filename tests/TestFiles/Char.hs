module Char where

char :: Char -> Int
char 'a' = 0
char _ = 1

f :: String -> Int
f (a:b:rest)
  | a <= b = 1
  | otherwise = 2
