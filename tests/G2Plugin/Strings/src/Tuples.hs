{-# LANGUAGE BangPatterns #-}

module Tuples where

import G2.Plugin

{-# ANN module ("--smt-tuples --smt-adts A")
    #-}

{-# ANN appTuple (SMTEquivIs "smtAppTuple")
    #-}
appTuple :: Int -> Int -> [(Int, Int)] -> [(Int, Int)]
appTuple x y [] = [(x, y)]
appTuple x y (t:ts) = t:appTuple x y ts

smtAppTuple :: Int -> Int -> [(Int, Int)] -> [(Int, Int)]
smtAppTuple x y ts = ts $++ [(x, y)]

{-# ANN appTupleBad (SMTEquivIs "smtAppTupleBad")
    #-}
appTupleBad :: Int -> Int -> [(Int, Int)] -> [(Int, Int)]
appTupleBad x y [] = [(x, y)]
appTupleBad x y (t:ts) = t:appTupleBad x y ts

smtAppTupleBad :: Int -> Int -> [(Int, Int)] -> [(Int, Int)]
smtAppTupleBad x y ts = ts $++ ts $++ [(x, y)]


data A = A | B

instance Eq A where
    A == A = True
    B == B = True
    _ == _ = False

{-# ANN pairA (SMTEquivIsWithConfig "smtPairA" "--log-pretty a_pair5 --no-log-files --print-smt --time 9999999999999")
    #-}
pairA :: [A] -> [(A, A)]
pairA [] = []
pairA (x:xs) = (x, A):pairA xs

smtPairA :: [A] -> [(A, A)]
smtPairA xs = genVal (\ys -> xs `smtEq` smtMap fst ys
                          && smtFoldLeft (\acc y -> acc && snd y == A) True ys)

{-
{-# ANN myZip (SMTEquivIsWithConfig "smtMyZip" "--print-smt")
    #-}
myZip :: [Int] -> [Int] -> [(Int, Int)]
myZip [] _ = []
myZip _ [] = []
myZip (x:xs) (y:ys) = (x, y):myZip xs ys

smtMyZip :: [Int] -> [Int] -> [(Int, Int)]
smtMyZip xs ys | smtLen xs < smtLen ys = smtFoldLeftI (\i ts x -> let !y = ys `smtNth` i in ts $++ [(x, y)]) 0 [] xs
               | otherwise = smtFoldLeftI (\i ts y -> let !x = xs `smtNth` i in ts $++ [(x, y)]) 0 [] ys
-}