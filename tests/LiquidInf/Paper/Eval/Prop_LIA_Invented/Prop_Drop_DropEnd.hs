module Prop_Drop_DropEnd (prop_drop_drop_end) where

import Prelude hiding (head, tail, length, drop)

{-@ prop_drop_drop_end :: n:{ _:Int | n >= 0 } -> { xs:[a] | len xs >= n } -> { v:Bool | v} @-}
prop_drop_drop_end :: Int -> [a] -> Bool
prop_drop_drop_end n xs =
    length xs == length (drop n xs) + length (dropEnd n xs)

length :: [a] -> Int
length [] = 0
length (_:xs) = 1 + length xs

drop :: Int -> [a] -> [a]
drop 0 xs     = xs
drop n (_:xs) = drop (n-1) xs
drop _ _      = die "drop"

dropEnd :: Int -> [a] -> [a]
dropEnd 0 _ = []
dropEnd n (x:xs) = x:dropEnd (n - 1) xs
dropEnd _ _ = die "dropEnd"

{-@ die :: {v:String | false} -> a @-}
die str = error str
