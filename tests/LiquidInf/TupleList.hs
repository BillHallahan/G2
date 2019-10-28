module TupleList where

import Prelude hiding (map)

{-@ sumNonNeg :: [({ x:Int | x >= 0}, Int)] -> { y:Int | y >= 0} @-}
sumNonNeg :: [(Int, Int)] -> Int
sumNonNeg = sumFst

{-@ sumFst :: [(Int, Int)] -> Int @-}
sumFst :: [(Int, Int)] -> Int
sumFst = foldr (+) 0 . map fst

{-@ len2 :: { xs:[Int] | len xs == 2 } @-}
len2 :: [Int]
len2 = [1, 2]

map :: (a -> b) -> [a] -> [b]
map _ [] = []
map f (x:xs) = f x:map f xs