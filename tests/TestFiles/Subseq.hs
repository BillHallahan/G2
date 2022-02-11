module Subseq where

isSubsequenceOf' :: [Int] -> [Int] -> Bool
isSubsequenceOf' [] _ = True
isSubsequenceOf' _ [] = False
isSubsequenceOf' a@(x:a') (y:b)
    | x == y    = isSubsequenceOf' a' b
    | otherwise = isSubsequenceOf' a b

subseqTest :: [Int] -> Bool
subseqTest b = (isSubsequenceOf' [1,2,3] b) && (length b > 3)

assume :: [Int] -> Bool -> Bool
assume _ b = b