module MoreTuples where

import G2.Plugin

{-# ANN module ("--smt-tuples")
    #-}

{-
{-# ANN listTuple (SMTEquivIsWithConfig "smtListTuple" "")
    #-}
listTuple :: [Int] -> [Int] -> ([Int], [Int])
listTuple xs ys = (xs ++ ys, ys ++ xs)
 
smtListTuple :: [Int] -> [Int] -> ([Int], [Int])
smtListTuple xs ys = (xs $++ ys, ys $++ xs)
-}

{-# ANN pairInt (SMTEquivIsWithConfig "smtPairInt" "")
    #-}
pairInt :: [Int] -> [(Int, Int)]
pairInt [] = []
pairInt (x:xs) = (x, 1):pairInt xs

smtPairInt :: [Int] -> [(Int, Int)]
smtPairInt xs = exists (\ys -> xs `smtEq` smtMap fst ys
                            && smtFoldLeft (\acc y -> acc && snd y == 1) True ys)

{-
{-# ANN pairInt' (SMTEquivIsWithConfig "smtPairInt'" "")
    #-}
pairInt' :: Int -> (Int, Int)
pairInt' x = (x, 1)

smtPairInt' :: Int -> (Int, Int)
smtPairInt' x = exists (\y -> fst y == x
                           && snd y == 1)
-}