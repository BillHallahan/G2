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

{-# ANN pairA (SMTEquivIsWithConfig "smtPairA" "")
    #-}
pairA :: [A] -> [(A, A)]
pairA [] = []
pairA (x:xs) = (x, A):pairA xs

smtPairA :: [A] -> [(A, A)]
smtPairA xs = genVal (\ys -> xs `smtEq` smtMap fst ys
                          && smtFoldLeft (\acc y -> acc && snd y == A) True ys)

{-# ANN pairABad (SMTEquivIsWithConfig "smtPairABad" "")
    #-}
pairABad :: [A] -> [(A, A)]
pairABad [] = []
pairABad (x:xs) = (x, B):pairA xs

smtPairABad :: [A] -> [(A, A)]
smtPairABad xs = genVal (\ys -> xs `smtEq` smtMap fst ys
                             && smtFoldLeft (\acc y -> acc && snd y == A) True ys)


{-# ANN myZip (SMTEquivIsWithConfig "smtMyZip" "--print-smt")
    #-}
myZip :: [A] -> [A] -> [(A, A)]
myZip [] _ = []
myZip _ [] = []
myZip (x:xs) (y:ys) = (x, y):myZip xs ys

smtMyZip :: [A] -> [A] -> [(A, A)]
smtMyZip xs ys | smtLen xs < smtLen ys = genVal (\zs -> xs `smtEq` smtMap fst zs 
                                                     && smtMap snd zs `smtPrefixOf` ys)
               | otherwise = genVal (\zs -> smtMap fst zs `smtPrefixOf` xs 
                                         && ys `smtEq` smtMap snd zs)


{-# ANN myZipBad (SMTEquivIsWithConfig "smtMyZipBad" "")
    #-}
myZipBad :: [A] -> [A] -> [(A, A)]
myZipBad [] _ = []
myZipBad _ [] = []
myZipBad (x:xs) (_:ys) = (x, x):myZipBad xs ys

smtMyZipBad :: [A] -> [A] -> [(A, A)]
smtMyZipBad xs ys | smtLen xs < smtLen ys = genVal (\zs -> xs `smtEq` smtMap fst zs 
                                                        && smtMap snd zs `smtPrefixOf` ys)
                  | otherwise = genVal (\zs -> smtMap fst zs `smtPrefixOf` xs 
                                            && ys `smtEq` smtMap snd zs)

{-# ANN myA (SMTEquivIsWithConfig "smtMyA" "")
    #-}
myA :: [A] -> [A] -> [A]
myA [] _ = []
myA _ [] = []
myA (x:xs) ys = x:myA xs ys

smtMyA :: [A] -> [A] -> [A]
smtMyA _ [] = []
smtMyA xs _ = genVal (\zs -> zs `smtEq` xs)
