module Take (prop_take) where

import Prelude hiding (length, take)

{-@ prop_take :: n:Nat -> { xs:[a] | len xs >= n } -> { v:Bool | v } @-}
prop_take :: Int -> [a] -> Bool
prop_take n xs = length (take n xs) == n 

length :: [a] -> Int
length [] = 0
length (x:xs) = 1 + length xs

take :: Int -> [a] -> [a]
take 0 _      = []
take n (x:xs) = x : take (n-1) xs
take _ _      = die "won't happen"

{-@ die :: {v:String | false} -> a @-}
die str = error ("Oops, I died!" ++ str)
