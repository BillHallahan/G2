module PathsTest1 where

import Data.Maybe

f xs = case xs of
    [] -> []
    [_] -> []
    (_:_) -> xs

test1 list = case f list of
    [] -> []
    _  -> list

len [] = 0
len (x:xs) = 1 + len xs

test2 list = case len list of 
    1 -> []
    _ -> list

test3 list = case [] of
    [] -> []
    _:_ -> list

data Tree a = Empty | Node a (Tree a) (Tree a)

data List a = Nil | a :> List a 

test4 :: List (Tree Int) -> Int
test4 xs = case xs of
    Nil -> 0
    (x :> xs') -> case x of
            Empty -> 0
            Node y left right -> if y > 0 then y else 2

test5 :: [Char] -> Char
test5 xs = case xs of
    [] -> 'e'
    'a':_ -> 'b'
    'c':_ -> 'z'
    _:_ -> 'a'

test6 :: Maybe (List Int) -> (List Int)
test6 x = case x of
    Just y -> case y of
        Nil -> Nil
        z :> Nil -> Nil
        _ :> _ -> y
    Nothing -> Nil