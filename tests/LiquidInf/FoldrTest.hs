module FoldrTest where

import Prelude hiding (foldr)

{-@ foldr :: (a -> b -> b) -> b -> [a] -> b @-}
foldr :: (a -> b -> b) -> b -> [a] -> b
foldr _ b [] = b
foldr op b (x:xs) = x `op` (foldr op b xs)

{-@ add :: Int -> Int -> Int @-}
add :: Int -> Int -> Int
add = (+)

{-@ sum :: [{x:Int | x > 0}] -> {y:Int | y >= 0} @-}
sum :: [Int] -> Int
sum = foldr add 0