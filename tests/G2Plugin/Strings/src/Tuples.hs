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

{-
data A = A

instance Eq A where
    A == A = True

{-# ANN pairZero (SMTEquivIsWithConfig "smtPairZero" "--print-smt")
    #-}
pairZero :: [A] -> [(A, A)]
pairZero [] = []
pairZero (x:xs) = (x, A):pairZero xs

smtPairZero :: [A] -> [(A, A)]
smtPairZero xs = genVal (\ys -> xs `smtEq` smtMap fst ys
                             && smtFoldLeft (\acc y -> acc && y == A) True (smtMap snd ys))
-}

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