module Strings where

import G2.Plugin

{-# ANN f (SMTEquivIs "f2" )
    #-}
f :: [Int] -> [Int]
f xs =
    let ys = [1] $++ xs in
    case smtLen ys > 7 of
        True -> ys
        False -> ys $++ ys

f2 :: [Int] -> [Int]
f2 xs =
    case smtLen xs > 6 of
        True -> [1] $++ xs
        False -> [1] $++ xs $++ [1] $++ xs

{-# ANN myApp (SMTEquivIs "app") #-}
myApp :: [Int] -> [Int] -> [Int]
myApp [] ys = ys
myApp (x:xs) ys = x:(myApp xs ys)

app :: [Int] -> [Int] -> [Int]
app xs ys = xs $++ ys

{-# ANN appMult (SMTEquivIs "smtAppMult") #-}
appMult :: [Int] -> [Int] -> [Int] -> [Int]
appMult xs ys zs = xs `myApp` ys `myApp` zs

smtAppMult :: [Int] -> [Int] -> [Int] -> [Int]
smtAppMult xs ys zs = xs $++ ys $++ zs


{-# ANN corr (SMTEquivIs "smtCorr") #-}
corr :: Int -> Int
corr = incorr

smtCorr :: Int -> Int
smtCorr x = x + 1

{-# ANN incorr (SMTEquivIs "smtIncorr") #-}
incorr :: Int -> Int
incorr x = x + 1

smtIncorr :: Int -> Int
smtIncorr x = x + 2

{-# ANN addOneAll (SMTEquivIs "smtAddOneAll") #-}
addOneAll :: [Int] -> [Int]
addOneAll [] = []
addOneAll (x:xs) = x + 1:addOneAll xs

smtAddOneAll :: [Int] -> [Int]
smtAddOneAll = smtMap (\x -> x + 1)

{-# ANN addTwoAll (SMTEquivIs "smtAddTwoAll") #-}
addTwoAll :: [Int] -> [Int]
addTwoAll [] = []
addTwoAll (x:xs) = x + 2:addOneAll xs -- Bug- calls addOneAll instead of addTwoAll

smtAddTwoAll :: [Int] -> [Int]
smtAddTwoAll xs = smtMap (\x -> x + 2) xs

{-
{-# ANN sumList (SMTEquivIsWithConfig "smtSumList" "--log-pretty a_sum") #-}
sumList :: [Int] -> Int
sumList [] = 0
sumList (x:xs) = x + sumList xs

smtSumList :: [Int] -> Int
smtSumList xs = smtFoldLeft (\x y -> x + y) 0 xs
-}

{-# ANN myIntersperse (SMTEquivIsWithConfig "smtMyIntersperse" "") #-}
myIntersperse :: Int -> [Int] -> [Int]
myIntersperse _ [] = []
myIntersperse _ [x] = [x]
myIntersperse x (y:ys) = y:x:myIntersperse x ys

smtMyIntersperse :: Int -> [Int] -> [Int]
smtMyIntersperse _ [] = []
smtMyIntersperse _ [x] = [x]
smtMyIntersperse x (i:ys) = i:smtFoldLeft (\acc y -> acc $++ [x] $++ [y]) [] ys

{-# ANN myIntersperseBad (SMTEquivIsWithConfig "smtMyIntersperseBad" "") #-}
myIntersperseBad :: Int -> [Int] -> [Int]
myIntersperseBad _ [] = []
myIntersperseBad _ [x] = [x]
myIntersperseBad x (y:ys) = y:x:myIntersperseBad y ys

smtMyIntersperseBad :: Int -> [Int] -> [Int]
smtMyIntersperseBad _ [] = []
smtMyIntersperseBad _ [x] = [x]
smtMyIntersperseBad x (i:ys) = i:smtFoldLeft (\acc y -> acc $++ [x] $++ [y]) [] ys

{-# ANN myRev (SMTEquivIsWithConfig "smtMyRev" "") #-}
myRev :: [Int] -> [Int]
myRev [] = []
myRev (y:ys) = myRev ys ++ [y]

smtMyRev :: [Int] -> [Int]
smtMyRev ys = smtFoldLeft (\acc y -> y:acc) [] ys

{-# ANN myRevBad (SMTEquivIsWithConfig "smtMyRevBad" "") #-}
myRevBad :: [Int] -> [Int]
myRevBad [] = []
myRevBad (y:ys) = myRev ys ++ [y]

smtMyRevBad :: [Int] -> [Int]
smtMyRevBad ys = smtFoldLeft (\acc y -> acc $++ [y]) [] ys
