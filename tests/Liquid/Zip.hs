{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}
module Zip where

import Prelude hiding (head, zip, concat, replicate)

{-@ measure size @-}
{-@ size :: [a] -> Nat @-}
size :: [a] -> Int
size []        = 0
size (x:xs) = 1 + size xs

{-@ head :: {xs:[a] | size xs > 0} -> a @-}
head :: [a] -> a
head (x:xs) = x
head [] = error "Bad call to head"

{-@ zip :: xs:[a] -> {ys:[b] | size xs > 0 => size ys > 0} -> [(a, b)] @-}
zip   :: [a] -> [b] -> [(a, b)]
zip [] [] = []
zip (x:xs) (y:ys) = (x, y):zip xs ys
zip _ _ = die  "Bad call to zip"

{-@ die :: {v:String | false} -> a @-}
die str = error ("Oops, I died!" ++ str)

{-@ measure sumsize @-}
sumsize [] = 0
sumsize (x:xs) = size x + sumsize xs

{-@ concat :: x:[[a]] -> {v : [a] | size v = sumsize x} @-}
concat [] = []
concat (xs:[]) = xs
concat (xs:(ys:xss)) = concat ((append xs ys):xss)

append [] [] = []
append xs [] = xs
append [] ys = ys
append (x:xs) ys  = x:append xs ys

{-@ replicate :: n:Int -> a -> { xs:[a] | size xs == n } @-}
replicate :: Int -> a -> [a]
replicate 0 x = []
replicate n x = x:replicate n x