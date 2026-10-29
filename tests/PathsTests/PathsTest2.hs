module PathsTest2 where

import Control.Exception

test1 xs = case xs of
    [] -> error "Failure"
    _:_ -> xs

test2 xs = case xs of
    [] -> []
    [x] -> assert (x > 1) [x]
    _:_ -> xs

test3 xs = case xs of
    [] -> []
    [x] -> case x of
            1 -> assert False [x]
            2 -> [x]
            _ -> []
    _:_ -> xs

data Tree a = Empty | Node a (Tree a) (Tree a)

data List a = Nil | a :> List a 

test4 :: List (Tree Int) -> Int
test4 xs = case xs of
    Nil -> assert False 0
    (x :> xs') -> case x of
            Empty -> 0
            Node y left right -> if y > 0 then y else 2