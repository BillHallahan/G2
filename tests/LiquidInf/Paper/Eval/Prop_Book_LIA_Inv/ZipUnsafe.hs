module ZipUnsafe (zip_prop) where

import Prelude hiding (length, zip)

{-@ zip_prop :: [a] -> [b] -> { v:Bool | v } @-}
zip_prop xs ys =
	let rs = zip xs ys in
	if length xs < length ys
		then length rs == length xs
		else length rs == length ys

length :: [a] -> Int
length [] = 0
length (x:xs) = 1 + length xs

zip :: [a] -> [b] -> [(a, b)]
zip (a:as) (b:bs) = (a, b) : zip as bs
zip [] _          = []
zip _  []         = []