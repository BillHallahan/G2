module Drop (prop_drop) where

import Prelude hiding (length, drop)

{-@ prop_drop :: n:Nat -> { xs:[a] | len xs >= n } -> { v:Bool | v } @-}
prop_drop :: Int -> [a] -> Bool
prop_drop n xs = length (drop n xs) == length xs - n

length :: [a] -> Int
length [] = 0
length (x:xs) = 1 + length xs

drop :: Int -> [a] -> [a]
drop 0 xs     = xs
drop n (_:xs) = drop (n-1) xs
drop _ _      = die "won't happen"

{-@ die :: {v:String | false} -> a @-}
die str = error ("Oops, I died!" ++ str)
