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

{-# ANN addTwoAll (SMTEquivIsWithConfig "smtAddTwoAll" "") #-}
addTwoAll :: [Int] -> [Int]
addTwoAll [] = []
addTwoAll (x:xs) = x + 2:addOneAll xs -- Bug- calls addOneAll instead of addTwoAll

smtAddTwoAll :: [Int] -> [Int]
smtAddTwoAll xs = smtMap (\x -> x + 2) xs
