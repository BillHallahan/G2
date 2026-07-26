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

{-# ANN sumList (SMTEquivIsWithConfig "smtSumList" "") #-}
sumList :: [Int] -> Int
sumList [] = 0
sumList (x:xs) = x + sumList xs

smtSumList :: [Int] -> Int
smtSumList xs = smtFoldLeft (\x y -> x + y) 0 xs

{-# ANN sumList2 (SMTEquivIsWithConfig "smtSumList2" "") #-}
sumList2 :: [Int] -> Int
sumList2 [] = 0
sumList2 (x:xs) = x + sumList xs

smtSumList2 :: [Int] -> Int
smtSumList2 xs = smtFoldLeft (\x y -> y + x) 0 xs

{-
{-# ANN sumListInit9 (SMTEquivIsWithConfig "smtSumListInit9" "") #-}
sumListInit9 :: [Int] -> Int
sumListInit9 [] = 9
sumListInit9 (x:xs) = x + sumListInit9 xs

smtSumListInit9 :: [Int] -> Int
smtSumListInit9 xs = smtFoldLeft (\x y -> x + y) 9 xs
-}

{-# ANN sumListBad (SMTEquivIsWithConfig "smtSumListBad" "") #-}
sumListBad :: [Int] -> Int
sumListBad [] = 0
sumListBad (x:xs) = x + sumListBad xs

smtSumListBad :: [Int] -> Int
smtSumListBad xs = smtFoldLeft (\x y -> x + y + 1) 0 xs

{-# ANN myIntersperse (SMTEquivIsWithConfig "smtMyIntersperse" "")
    #-}
myIntersperse :: Int -> [Int] -> [Int]
myIntersperse _ [] = []
myIntersperse _ [x] = [x]
myIntersperse x (y:ys) = y:x:myIntersperse x ys

smtMyIntersperse :: Int -> [Int] -> [Int]
smtMyIntersperse _ [] = []
smtMyIntersperse _ [x] = [x]
smtMyIntersperse x (i:ys) = i:smtFoldLeft (\acc y -> acc $++ ([x] $++ [y])) [] ys

{-# ANN myIntersperse2 (SMTEquivIsWithConfig "smtMyIntersperse2" "")
    #-}
myIntersperse2 :: Int -> [Int] -> [Int]
myIntersperse2 _ [] = []
myIntersperse2 _ [x] = [x]
myIntersperse2 x (y:ys) = y:x:x:myIntersperse2 x ys

smtMyIntersperse2 :: Int -> [Int] -> [Int]
smtMyIntersperse2 _ [] = []
smtMyIntersperse2 _ [x] = [x]
smtMyIntersperse2 x (i:ys) = i:smtFoldLeft (\acc y -> ((acc $++ [x]) $++ [x]) $++ [y]) [] ys

{-# ANN myIntersperseBad (SMTEquivIsWithConfig "smtMyIntersperseBad" "") #-}
myIntersperseBad :: Int -> [Int] -> [Int]
myIntersperseBad _ [] = []
myIntersperseBad _ [x] = [x]
myIntersperseBad x (y:ys) = y:x:myIntersperseBad y ys

smtMyIntersperseBad :: Int -> [Int] -> [Int]
smtMyIntersperseBad _ [] = []
smtMyIntersperseBad _ [x] = [x]
smtMyIntersperseBad x (i:ys) = i:smtFoldLeft (\acc y -> acc $++ [x] $++ [y]) [] ys

{-# ANN myIntersperseBegin (SMTEquivIs "smtMyIntersperseBegin")
    #-}
myIntersperseBegin :: Int -> [Int] -> [Int]
myIntersperseBegin x [] = [x]
myIntersperseBegin x [y] = [x, y]
myIntersperseBegin x (y:ys) = x:y:myIntersperseBegin x ys

smtMyIntersperseBegin :: Int -> [Int] -> [Int]
smtMyIntersperseBegin x [] = [x]
smtMyIntersperseBegin x [y] = [x, y]
smtMyIntersperseBegin x ys = smtFoldLeft (\acc y -> acc $++ ([x, y])) [] ys

{-# ANN myIntersperseBegin2 (SMTEquivIs "smtMyIntersperseBegin2")
    #-}
myIntersperseBegin2 :: Int -> [Int] -> [Int]
myIntersperseBegin2 x [] = [x]
myIntersperseBegin2 x [y] = [x, y]
myIntersperseBegin2 x (y:ys) = x:y:myIntersperseBegin2 x ys

smtMyIntersperseBegin2 :: Int -> [Int] -> [Int]
smtMyIntersperseBegin2 x [] = [x]
smtMyIntersperseBegin2 x [y] = [x, y]
smtMyIntersperseBegin2 x (y:ys) = smtFoldLeft (\acc y' -> acc $++ ([x, y'])) [x, y] ys

{-# ANN myIntersperseBeginBad (SMTEquivIs "smtMyIntersperseBeginBad")
    #-}
myIntersperseBeginBad :: Int -> [Int] -> [Int]
myIntersperseBeginBad x [] = [x]
myIntersperseBeginBad x [y] = [x, y]
myIntersperseBeginBad x (y:ys) = x:y:myIntersperseBeginBad x ys

smtMyIntersperseBeginBad :: Int -> [Int] -> [Int]
smtMyIntersperseBeginBad x [] = [x]
smtMyIntersperseBeginBad x [y] = [x, y]
smtMyIntersperseBeginBad x (y:ys) = smtFoldLeft (\acc y' -> acc $++ ([x, y])) [x, y] ys

{-# ANN myIntersperseApp1 (SMTEquivIsWithConfig "smtMyIntersperseApp1" "")
    #-}
myIntersperseApp1 :: Int -> [Int] -> [Int]
myIntersperseApp1 x xs = [1] ++ myIntersperse x xs

smtMyIntersperseApp1 :: Int -> [Int] -> [Int]
smtMyIntersperseApp1 _ [] = [1]
smtMyIntersperseApp1 _ [x] = [1, x]
smtMyIntersperseApp1 x (i:ys) = smtFoldLeft (\acc y -> acc $++ ([x] $++ [y])) [1, i] ys

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