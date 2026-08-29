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
smtPairA xs = exists (\ys -> xs `smtEq` smtMap fst ys
                          && smtFoldLeft (\acc y -> acc && snd y == A) True ys)

{-# ANN pairABad (SMTEquivIsWithConfig "smtPairABad" "")
    #-}
pairABad :: [A] -> [(A, A)]
pairABad [] = []
pairABad (x:xs) = (x, B):pairA xs

smtPairABad :: [A] -> [(A, A)]
smtPairABad xs = exists (\ys -> xs `smtEq` smtMap fst ys
                             && smtFoldLeft (\acc y -> acc && snd y == A) True ys)

{-# ANN myZip (SMTEquivIsWithConfig "smtMyZip" "--smt-timeout 20")
    #-}
myZip :: [A] -> [A] -> [(A, A)]
myZip [] _ = []
myZip _ [] = []
myZip (x:xs) (y:ys) = (x, y):myZip xs ys

smtMyZip :: [A] -> [A] -> [(A, A)]
smtMyZip xs ys | smtLen xs < smtLen ys = exists (\zs -> xs `smtEq` smtMap fst zs 
                                                     && smtMap snd zs `smtPrefixOf` ys)
               | otherwise = exists (\zs -> smtMap fst zs `smtPrefixOf` xs 
                                         && ys `smtEq` smtMap snd zs)

{-# ANN myZipBad (SMTEquivIsWithConfig "smtMyZipBad" "")
    #-}
myZipBad :: [A] -> [A] -> [(A, A)]
myZipBad [] _ = []
myZipBad _ [] = []
myZipBad (x:xs) (_:ys) = (x, x):myZipBad xs ys

smtMyZipBad :: [A] -> [A] -> [(A, A)]
smtMyZipBad xs ys | smtLen xs < smtLen ys = exists (\zs -> xs `smtEq` smtMap fst zs 
                                                        && smtMap snd zs `smtPrefixOf` ys)
                  | otherwise = exists (\zs -> smtMap fst zs `smtPrefixOf` xs 
                                            && ys `smtEq` smtMap snd zs)

{-# ANN myA (SMTEquivIsWithConfig "smtMyA" "")
    #-}
myA :: [A] -> [A] -> [A]
myA [] _ = []
myA _ [] = []
myA (x:xs) ys = x:myA xs ys

smtMyA :: [A] -> [A] -> [A]
smtMyA _ [] = []
smtMyA xs _ = exists (\zs -> zs `smtEq` xs)

{-# ANN myUnzip (SMTEquivIsWithConfig "smtMyUnzip" "")
    #-}
myUnzip :: [(A, A)] -> [A] -> [A] -> ([A], [A])
myUnzip [] xs ys = (myRev xs, myRev ys)
myUnzip ((x, y):xs_ys) xs ys = myUnzip xs_ys (x:xs) (y:ys)

smtMyUnzip :: [(A, A)] -> [A] -> [A] -> ([A], [A])
smtMyUnzip xs_ys xs ys =
    let (as', bs') = exists2 (\as bs -> as `smtEq` smtMap fst xs_ys 
                                     && bs `smtEq` smtMap snd xs_ys)
    in
    (smtMyRev xs $++ as', smtMyRev ys $++ bs')

{-# ANN myRev (SMTEquivIsWithConfig "smtMyRev" "") #-}
myRev :: [A] -> [A]
myRev [] = []
myRev (y:ys) = myRev ys ++ [y]

smtMyRev :: [A] -> [A]
smtMyRev ys = smtFoldLeft (\acc y -> y:acc) [] ys

{-
{-# ANN myLookup (SMTEquivIsWithConfig "smtMyLookup" "--print-smt")
    #-}
myLookup :: A -> [(A, A)] -> Maybe A
myLookup _ [] = Nothing
myLookup x ((y, z):ys) | x == y = Just z
                       | otherwise = myLookup x ys

smtMyLookup :: A -> [(A, A)] -> Maybe A
smtMyLookup x xs
    | not (smtContains fst_xs [x]) = Nothing
    | otherwise =
        let
            (ys', _) = exists2 (\ys zs -> ys $++ zs `smtEq` fst_xs
                                       && not (smtContains ys [x])
                                       && smtAt zs 0 `smtEq` [x])
        in
        Just $ smtNth snd_xs (smtLen ys')
        where
            fst_xs = smtMap fst xs
            snd_xs = smtMap snd xs
-}

{-# ANN myLookupBad (SMTEquivIsWithConfig "smtMyLookupBad" "")
    #-}
myLookupBad :: A -> [(A, A)] -> Maybe A
myLookupBad _ [] = Nothing
myLookupBad x ((y, z):ys) | x == y = Just z
                       | otherwise = myLookupBad x ys

smtMyLookupBad :: A -> [(A, A)] -> Maybe A
smtMyLookupBad x xs
    | not (smtContains fst_xs [x]) = Nothing
    | otherwise =
        let
            (ys', _) = exists2 (\ys zs -> ys ++ zs == fst_xs
                                    -- && not (smtContains ys [x])
                                       && smtAt zs 0 == [x])
        in
        Just $ smtNth snd_xs (smtLen ys')
        where
            fst_xs = smtMap fst xs
            snd_xs = smtMap snd xs

