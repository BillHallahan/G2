module PathsTest1 where

import Data.Maybe
import Data.List

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

infixr 5 :>

data Tree a = Empty | Node a (Tree a) (Tree a)

data ListNew a = Nil | a :> ListNew a deriving Eq

{-# NOINLINE duplicate #-}
duplicate :: ListNew Int -> ListNew Int
duplicate xs = case xs of
    Nil -> Nil
    x :> xs' -> x :> x :> duplicate xs'

test4 :: ListNew (Tree Int) -> Int
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

test6 :: Maybe (ListNew Int) -> (ListNew Int)
test6 x = case x of
    Just y -> case y of
        Nil -> Nil
        z :> Nil -> Nil
        _ :> _ -> y
    Nothing -> Nil

{-# NOINLINE g #-}
g :: ListNew Int -> Bool
g xs = case xs of 
    Nil -> False
    x :> xs' -> case xs' of
        Nil -> True
        x' :> xs'' -> case xs'' of
            Nil -> True
            _ :> _ -> False

{-# NOINLINE h #-}
h :: ListNew Int -> Bool
h xs = case xs of
    Nil -> False
    x :> xs' -> case xs' of
        Nil -> True
        x' :> xs'' -> False

test7 :: ListNew Int -> ListNew Int
test7 xs = case g xs of
    True -> Nil
    False -> xs

test8 :: ListNew Int -> ListNew Int
test8 xs = case h xs of
    True -> Nil
    False -> xs

test9 :: ListNew Int -> Int
test9 xs = case xs of
    Nil -> 0
    x :> xs' -> x + 5

test10 :: Maybe (ListNew Int) -> (Int, ListNew Int)
test10 x = case x of
    Just ys -> case ys of
        Nil -> (0, ys)
        z :> Nil -> (1, ys)
        z' :> ys'  -> 
            let 
                a = z' + 1 
                ys'' = duplicate ys'
            in (a, ys'')
    Nothing -> (3, Nil)

test11 xs = case xs of
    [] -> []
    x : xs' -> let 
        xs'' = reverse xs'
        xs''' = xs'' ++ xs'
        in intersperse x xs'''