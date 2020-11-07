module Concat where

import Prelude hiding (length, concat)

{-@ measure size @-}
size :: [a] -> Int
size [] = 0
size (x:xs) = 1 + size xs

{-@ invariant {v:[a] | 0 <= size v} @-}
{-@ invariant {v:[a] | len v == size v} @-}

{-@ measure sumsize @-}
sumsize :: [[a]] -> Int
sumsize [] = 0
sumsize (xs:xss)   = size xs + sumsize xss
    
concat :: [[a]] -> [a]
concat [] = []
concat [xs] = xs
concat (xs:ys:xss) = concat ((append xs ys):xss)

append :: [a] -> [a] -> [a]
append xs [] = xs
append [] ys = ys
append (x:xs) ys = x:append xs ys

{-@ prop_concat :: { v:Bool | v } @-}
prop_concat :: Bool
prop_concat =
    let
        xss = [[1, 2], [3, 4], [5]]
    in
    size (concat xss) == 5
