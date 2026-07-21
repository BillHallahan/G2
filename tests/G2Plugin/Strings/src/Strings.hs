module Strings where

import G2.Plugin

{-# ANN f (SMTEquivIs "f2" )
    #-}
f :: [Int] -> [Int]
f xs =
    let ys = [1] +++ xs in
    case smtLen ys > 7 of
        True -> ys
        False -> ys +++ ys

f2 :: [Int] -> [Int]
f2 xs =
    case smtLen xs > 6 of
        True -> [1] +++ xs
        False -> [1] +++ xs +++ [1] +++ xs

{-# ANN myApp (SMTEquivIsWithConfig "app" "") #-}
myApp :: [Int] -> [Int] -> [Int]
myApp [] ys = ys
myApp (x:xs) ys = x:(myApp xs ys)

app :: [Int] -> [Int] -> [Int]
app xs ys = xs +++ ys