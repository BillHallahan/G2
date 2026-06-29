module Test where 

-- import Data.List
import GHC.Stack
import Control.Exception
import Prelude hiding (reverse, last, elem, map)

my_reverse :: String -> String
my_reverse []     = []
my_reverse (x:xs) = my_reverse xs ++ [x]

elem :: Char -> String -> Bool
elem _ []     = False
elem y (x:xs)
  | y == x    = True
  | otherwise = elem y xs

-- TO-DO: Synthesizer for specification, does not support exception yet
-- last :: String -> Char
-- last [x]    = x
-- last (_:xs) = last xs

delete :: Char -> String -> String
delete  _ []        = []
delete x (y:ys)    = if x == y then ys else y : delete x ys


-- Throwing error for String: (error "Parse Error: <stdin>:14.22: Non-printable character in string literal")
-- Throwinf error for Ints: (error "invalid grammar, must have at least one rule for each non-terminal symbol")
insert :: Int -> [Int] -> [Int]
insert x [] = [x]
insert x ys@(y:ys')
 = case compare x y of
     GT -> y : insert x ys'
     _  -> x : ys
