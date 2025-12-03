module Char where

import Data.Char

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

isDigitTest :: Char -> (Bool, Int)
isDigitTest c | isDigit c = (True, 0)
              | otherwise = (False, 1)

toUp :: Char -> (Int, Char)
toUp c | 'w' < c = (1, toUpper c)
       | 'm' < c = (2, toUpper c)
       | 'f' < c = (3, toUpper c)
       | 'a' <= c = (4, toUpper c)
       | isUpper c = (5, toUpper c)
       | otherwise = (6, toUpper c)

toLow :: Char -> (Int, Char)
toLow c | isLower c = (5, toLower c)
        | 'W' < c = (1, toLower c)
        | 'M' < c = (2, toLower c)
        | 'F' < c = (3, toLower c)
        | 'A' <= c = (4, toLower c)
        | otherwise = (6, toLower c)