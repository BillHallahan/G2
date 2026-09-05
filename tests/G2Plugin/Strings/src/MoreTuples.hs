module MoreTuples where

import G2.Plugin
import G2.Plugin.Unsafe

{-# ANN module ("--smt-tuples")
    #-}

{-# ANN listTuple (SMTEquivIsWithConfig "smtListTuple" "")
    #-}
listTuple :: [Int] -> [Int] -> ([Int], [Int])
listTuple xs ys = (xs ++ ys, ys ++ xs)
 
smtListTuple :: [Int] -> [Int] -> ([Int], [Int])
smtListTuple xs ys = (xs $++ ys, ys $++ xs)

{-# ANN pairInt (SMTEquivIsWithConfig "smtPairInt" "")
    #-}
pairInt :: [Int] -> [(Int, Int)]
pairInt [] = []
pairInt (x:xs) = (x, 1):pairInt xs

smtPairInt :: [Int] -> [(Int, Int)]
smtPairInt xs = exists (\ys -> xs `smtEq` smtMap fst ys
                            && smtFoldLeft (\acc y -> acc && snd y == 1) True ys)

{-# ANN pairInt' (SMTEquivIsWithConfig "smtPairInt'" "")
    #-}
pairInt' :: Int -> (Int, Int)
pairInt' x = (x, 1)

smtPairInt' :: Int -> (Int, Int)
smtPairInt' x = exists (\y -> fst y == x
                           && snd y == 1)

{-# ANN myZipInt (SMTEquivIsWithConfig "smtMyZipInt" "")
    #-}
myZipInt :: [Int] -> [Int] -> [(Int, Int)]
myZipInt [] _ = []
myZipInt _ [] = []
myZipInt (x:xs) (y:ys) = (x, y):myZipInt xs ys

smtMyZipInt :: [Int] -> [Int] -> [(Int, Int)]
smtMyZipInt xs ys | smtLen xs < smtLen ys = exists (\zs -> xs `smtEq` smtMap fst zs 
                                                        && smtMap snd zs `smtPrefixOf` ys)
                  | otherwise = exists (\zs -> smtMap fst zs `smtPrefixOf` xs 
                                         && ys `smtEq` smtMap snd zs)

{-# ANN myZipBadInt (SMTEquivIsWithConfig "smtMyZipBadInt" "")
    #-}
myZipBadInt :: [Int] -> [Int] -> [(Int, Int)]
myZipBadInt [] _ = []
myZipBadInt _ [] = []
myZipBadInt (x:xs) (_:ys) = (x, x):myZipBadInt xs ys

smtMyZipBadInt :: [Int] -> [Int] -> [(Int, Int)]
smtMyZipBadInt xs ys | smtLen xs < smtLen ys = exists (\zs -> xs `smtEq` smtMap fst zs 
                                                           && smtMap snd zs `smtPrefixOf` ys)
                     | otherwise = exists (\zs -> smtMap fst zs `smtPrefixOf` xs 
                                               && ys `smtEq` smtMap snd zs)

{-# ANN myUnzipInt (SMTEquivIsWithConfig "smtMyUnzipInt" "")
    #-}
myUnzipInt :: [(Int, Int)] -> [Int] -> [Int] -> ([Int], [Int])
myUnzipInt [] xs ys = (myRevInt xs, myRevInt ys)
myUnzipInt ((x, y):xs_ys) xs ys = myUnzipInt xs_ys (x:xs) (y:ys)

smtMyUnzipInt :: [(Int, Int)] -> [Int] -> [Int] -> ([Int], [Int])
smtMyUnzipInt xs_ys xs ys =
    let (as', bs') = exists2 (\as bs -> as `smtEq` smtMap fst xs_ys 
                                     && bs `smtEq` smtMap snd xs_ys)
    in
    (smtMyRevInt xs $++ as', smtMyRevInt ys $++ bs')

{-# ANN myRevInt (SMTEquivIsWithConfig "smtMyRevInt" "") #-}
myRevInt :: [Int] -> [Int]
myRevInt [] = []
myRevInt (y:ys) = myRevInt ys ++ [y]

smtMyRevInt :: [Int] -> [Int]
smtMyRevInt ys = smtFoldLeft (\acc y -> y:acc) [] ys
