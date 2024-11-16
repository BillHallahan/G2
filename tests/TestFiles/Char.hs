module Char where

char :: Char -> Int
char 'a' = 0
char _ = 1

f :: String -> Int
f (a:b:rest)
  | a <= b = 1
  | otherwise = 2

g :: String -> [String]
g ('[':_) = ["A"]
g (']':_) = ["B"]
g ('{':_) = ["C"]
g ('}':_) = ["D"]
g ('<':_) = ["E"]
g ('>':_) = ["F"]
g _ = []
