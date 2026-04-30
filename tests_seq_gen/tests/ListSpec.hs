module Test where

-- import Data.List
import GHC.Stack
import Control.Exception
import Prelude hiding (reverse, last)

my_reverse :: String -> String
my_reverse []     = []
my_reverse (x:xs) = my_reverse xs ++ [x]

-- reverse :: String -> String
-- reverse []     = []
-- reverse (x:xs) = (let ys = symgen :: String in assume (spec_reverse xs ys) ys) ++ [x]


-- elem :: Char -> String -> Bool
-- elem _ []     = False
-- elem y (x:xs)
--   | y == x    = True
--   | otherwise = elem y xs

last :: String -> Char
last [x]    = x
last (_:xs) = last xs