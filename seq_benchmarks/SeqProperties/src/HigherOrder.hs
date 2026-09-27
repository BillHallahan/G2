module HigherOrder where

import G2.Plugin hiding ((==>))
import Prelude (Bool (..), Num (..), Eq (..), Ord(..), Int, (.), (&&), (||), otherwise)

{-# ANN module ("--smt-tuples --higher-order uninterpreted")
    #-}

infixr 0 ==>

given :: Bool -> Bool -> Bool
given pb pa = (not pb) || pa

(==>) :: Bool -> Bool -> Bool
(==>) = given

not :: Bool -> Bool
not True = False
not False = True

{-# ANN (++) (SMTEquivIs "appendSMT") #-}
(++) :: [a] -> [a] -> [a]
[] ++ ys = ys
(x:xs) ++ ys = x : (xs ++ ys)

appendSMT :: [a] -> [a] -> [a]
appendSMT = ($++)

{-# ANN len (SMTEquivIs "lenSMT") #-}
len :: [a] -> Int
len [] = 0
len (_:xs) = 1 + (len xs)

lenSMT :: [a] -> Int
lenSMT = smtLen

{-# ANN indexWithDefault (SMTEquivIs "indexWithDefaultSMT") #-}
indexWithDefault :: a -> [a] -> Int -> a
indexWithDefault d [] _ = d
indexWithDefault d (x:xs) n
    | n < 0 = d 
    | n == 0 = x
    | otherwise = indexWithDefault d xs (n - 1)

indexWithDefaultSMT :: a -> [a] -> Int -> a
indexWithDefaultSMT d xs n
    | 0 <= n, n < smtLen xs = smtNth xs n
    | otherwise = d 

{-# ANN concat (SMTEquivIs "concatSMT") #-}
concat :: [[a]] -> [a]
concat [] = []
concat (x:xs) = x ++ concat xs

concatSMT :: [[a]] -> [a]
concatSMT = smtConcat

{-# ANN map (SMTEquivIs "mapSMT") #-}
map :: (a -> b) -> [a] -> [b]
map _ [] = []
map f (x:xs) = (f x) : (map f xs)

mapSMT :: (a -> b) -> [a] -> [b]
mapSMT = smtMap

{-# ANN filter (SMTEquivIs "filterSMT") #-}
filter :: (a -> Bool) -> [a] -> [a]
filter _ [] = []
filter p (x:xs) =
  case p x of
    True -> x : (filter p xs)
    _ -> filter p xs

filterSMT :: (a -> Bool) -> [a] -> [a]
filterSMT p xs = smtFoldLeft (\acc e -> if p e then acc $++ [e] else acc) [] xs

{-# ANN concatMap (SMTEquivIs "concatMapSMT") #-}
concatMap :: (a -> [b]) -> [a] -> [b]
concatMap _ [] = []
concatMap f (x:xs) = f x ++ concatMap f xs

concatMapSMT :: (a -> [b]) -> [a] -> [b]
concatMapSMT f = smtConcat . smtMap f

{-# ANN any (SMTEquivIs "anySMT") #-}
any :: (a -> Bool) -> [a] -> Bool
any _ [] = False
any p (x:xs) = p x || any p xs

anySMT :: (a -> Bool) -> [a] -> Bool
anySMT = smtAny

{-# ANN all (SMTEquivIs "allSMT") #-}
all :: (a -> Bool) -> [a] -> Bool
all _ [] = True
all p (x:xs) = p x && all p xs

allSMT :: (a -> Bool) -> [a] -> Bool
allSMT = smtAll

{-# ANN intersperse (SMTEquivIs "intersperseSMT") #-}
intersperse :: a -> [a] -> [a]
intersperse _ [] = []
intersperse _ [y] = [y]
intersperse x (y:ys) = y:x:intersperse x ys

intersperseSMT :: a -> [a] -> [a]
intersperseSMT _ [] = []
intersperseSMT x (y:ys) = y:smtFoldLeft (\acc y_ -> acc ++ [x, y_]) [] ys

{-# ANN prop_01 Prop #-}
prop_01 :: (Int -> [Int]) -> [Int] -> Bool
prop_01 f xs = concat (map f xs) == concatMap f xs

{-# ANN prop_02 Prop #-}
prop_02 :: (Int -> Int) -> (Int -> Bool) -> [Int] -> Bool
prop_02 f p xs = filter p (map f xs) == map f (filter (p . f) xs)

{-# ANN prop_03 Prop #-}
prop_03 :: [Int] -> Bool
prop_03 xs = all (>= 0) xs ==> all (> 0) (map (+ 1) xs)

{-# ANN prop_04 Prop #-}
prop_04 :: [Int] -> Bool
prop_04 xs = any (>= 0) xs ==> any (> 0) (map (+ 1) xs)

{-# ANN prop_05 Prop #-}
prop_05 :: Int -> Int -> [Int] -> Bool
prop_05 ind x ys = 0 < ind && ind < len ys ==> indexWithDefault (-1) (intersperse x ys) (ind * 2 - 1) == x

{-# ANN prop_05_bad Prop #-}
prop_05_bad :: Int -> Int -> [Int] -> Bool
prop_05_bad ind x ys = 0 < ind && ind <= len ys ==> indexWithDefault (-1) (intersperse x ys) (ind * 2 - 1) == x