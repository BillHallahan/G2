module List1 where

import Data.List

infixr 0 ==>

(==>) :: Bool -> Bool -> Bool
True ==> False = False
_ ==> _ = True

infixr 0 `eqLen`

eqLen :: [()] -> [()] -> Bool
eqLen [] [] = True
eqLen (_:xs) (_:ys) = eqLen xs ys
eqLen _ _ = False

prop1 :: [()] -> Bool
prop1 xs = xs `eqLen` xs

prop2 :: [Int] -> Bool
prop2 xs = [] ++ xs == xs

prop3 :: [Int] -> Bool
prop3 xs = xs ++ [] == xs

prop4 :: [Int] -> [Int] -> Bool
prop4 (_:_) _ = True
prop4 xs ys = xs ++ ys == ys

prop5 :: [Int] -> Int -> Bool
prop5 xs x = xs < xs ++ [x]

prop6 :: [Int] -> [Int] -> Bool
prop6 xs ys = xs <= xs ++ ys

prop7Simple :: [()] -> [()] -> Bool
prop7Simple xs ys = xs ++ ys `eqLen` xs ++ ys

prop7 :: [Int] -> [Int] -> [Int] -> Bool
prop7 xs ys zs = (xs ++ ys) ++ zs == xs ++ (ys ++ zs)

prop8 :: Int -> [Int] -> Bool
prop8 x xs = x `elem'` xs ==> x `elem'` xs

elem' :: Int -> [Int] -> Bool
elem' x [] = False
elem' x (y:ys) = if x == y then True else elem' x ys

prop9 :: Int -> [Int] -> [Int] -> Bool
prop9 x xs ys = (x `elem'` xs) ==> (x `elem'` (xs ++ ys))

prop10 :: [Int] -> [Int] -> Bool
prop10 _ [] = True
prop10 xs ys = last ys == last (xs ++ ys)

prop11 :: Int -> [Int] -> Bool
prop11 n xs = take n xs ++ drop n xs == xs

prop12 :: Int -> [Int] -> Bool
prop12 x xs = x `notElem` deleteAll x xs

deleteAll :: Int -> [Int] -> [Int]
deleteAll x (y:ys) | x == y = deleteAll x ys
                   | otherwise = y:deleteAll x ys

prop4False :: [Int] -> [Int] -> Bool
prop4False (_:_:_) _ = True
prop4False xs ys = xs ++ ys == ys

prop5False :: [Int] -> Int -> Bool
prop5False xs x = xs < xs

prop6False :: [Int] -> [Int] -> Bool
prop6False xs ys = xs < xs ++ ys

prop7False :: [Int] -> [Int] -> [Int] -> Bool
prop7False xs ys zs = (xs ++ ys) ++ zs == xs ++ (zs ++ ys)

prop9False :: Int -> [Int] -> [Int] -> Bool
prop9False x xs ys = (x `elem'` xs) ==> (x `elem'` ys)

prop10False :: [Int] -> [Int] -> Bool
prop10False _ [] = True
prop10False xs ys = last ([1, 2, 3, 4, 5, 6, 7, 8, 9] ++ ys) == last (xs ++ [1, 2, 3, 4, 5, 6, 7, 8, 9])
