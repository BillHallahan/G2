module Seq1 where

import Data.List

-- Validation
floatEq :: (Eq a, RealFloat a) => a -> a -> Bool
floatEq x y | isNaN x, isNaN y = True
            | isInfinite x, isInfinite y = True
            | otherwise = x == y

floatListEq :: (Eq a, RealFloat a) => [a] -> [a] -> Bool
floatListEq [] [] = True
floatListEq (x:xs) (y:ys) = floatEq x y && xs `floatListEq` ys
floatListEq _ _ = False

newtype NIE a = NIE [a]

instance (Eq a, RealFloat a) => Eq (NIE a) where
    NIE x == NIE y = floatListEq x y

nieWrapSnd :: (a, [b]) -> (a, NIE b)
nieWrapSnd (x, y) = (x, NIE y)

-- Tests

toEnum1 :: [Int]
toEnum1 = [toEnum 56089]

conInt :: [Int] -> [Int] -> [Int]
conInt xs ys = xs ++ ys

conInteger :: [Integer] -> [Integer] -> [Integer]
conInteger xs ys = xs ++ ys

conFloat :: [Float] -> [Float] -> [Float]
conFloat xs ys = xs ++ ys

conDouble :: [Double] -> [Double] -> [Double]
conDouble xs ys = xs ++ ys

appendEq :: [Int] -> [Int]
appendEq s = s ++ [1]

listLen :: [Int] -> (Int, Bool)
listLen xs = let l = length xs in (l, case l > 5 of True -> False; False -> True)

listLen2 :: [Float] -> (Int, Bool)
listLen2 s =
    case s of
        (c:s) ->
            let l = length (c:s) in
            if l > 4 then (l, True) else (l, False)
        [] -> (1000, False)
    
listLen3 :: Double -> [Double] -> (Int, Bool)
listLen3 c s =
    let l = length (c:s) in
    if l > 4 then (l, True) else (l, False)

listApp :: [Int] -> [Int] -> Int
listApp xs ys = case xs ++ ys of
                    [1, 2, 3, 4, 5, 6, 7, 8, 9] -> 2
                    [9, 8, 7, 6, 5, 4] -> 1
                    _ -> 0

con2 :: Num a => [a] -> [a] -> (Int, [a])
con2 xs ys = case xs ++ ys of
    xs@(_:_:_) -> (3, xs)
    xs@(_:_) -> (2, xs)
    [] -> (1, [])

con2Int :: [Int] -> [Int] -> (Int, [Int])
con2Int = con2
con2Integer :: [Integer] -> [Integer] -> (Int, [Integer])
con2Integer = con2
con2Float :: [Float] -> [Float] -> (Int, NIE Float)
con2Float x y = nieWrapSnd (con2 x y)
con2Double :: [Double] -> [Double] -> (Int, NIE Double)
con2Double x y = nieWrapSnd (con2 x y)

con3 :: (Eq a, Num a) => [a] -> (Int, [a])
con3 xs
    | [] <- xs = (0, xs)
    | (y:ys) <- xs
    , 1:ys ++ ys == xs = (1, ys)
    | otherwise = (2, xs)

con3Int :: [Int] -> (Int, [Int])
con3Int = con3
con3Integer :: [Integer] -> (Int, [Integer])
con3Integer = con3
con3Float :: [Float] -> (Int, NIE Float)
con3Float = nieWrapSnd . con3
con3Double :: [Double] -> (Int, NIE Double)
con3Double = nieWrapSnd . con3

strIndex :: [Integer] -> (Bool, String)
strIndex str =
    case str !! 50 of
        3 -> (True, "Three")
        2 -> (False, "Two")
        _ -> (False, "None")

taker1 :: [Int] -> (Bool, [Int])
taker1 str = case t == [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 1, 1, 1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16] of
                True -> (False, t)
                False -> (True, t)
    where
        t = take 30 str

taker2 :: [Int] -> (Bool, [Int])
taker2 str = case t == [1, 42] of
                True -> (False, t)
                False -> (True, t)
    where
        t = take 22 str

inf :: [Int]
inf = inf

takeInf :: Int -> [Int]
takeInf _ = take 0 inf

takeUndefined :: Int -> [Int]
takeUndefined _ = take 0 undefined

-- ...

init1 :: [Int] -> (Int, [Int])
init1 xs | length xs < 20 = (1, init xs)
         | length xs < 40 = (2, init xs)
         | otherwise = (3, init xs)

null1 :: [Integer] -> Int
null1 xs =
    case null xs of
        True -> case null (xs ++ xs) of
                    True -> 1
                    False -> error "Impossible"
        False -> 2

last1 :: [Int] -> (Int, Int)
last1 xs | length xs > 50 = (1, last xs)
         | length xs > 30 = (2, last xs)
         | otherwise = (3, last xs)

drop1 :: [Int] -> (Bool, [Int])
drop1 str = case d == [1, 2, 3, 4, 5, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] of
                False -> (True, d)
                True -> (False, d)
    where
        d = drop 50 str

drop2 :: [Int] -> (Bool, [Int])
drop2 str = case d == [100, 200] of
                True -> (False, d)
                False -> (True, d)
    where
        d = drop 22 str

drop3 :: [Float] -> Int
drop3 str = case drop 20 str of
                [] | length str /= 20 -> 1
                   | str /= [] -> 2
                _ -> 3

elem1 :: [Int] -> Int -> (Bool, String)
elem1 str ch = case elem ch str of
                    True -> (False, "Switched")
                    False -> (True, "Opposite Day!")

notElem1 :: [Int] -> Int -> Int -> String
notElem1 str c1 c2 = case notElem c1 str of
                            True -> case notElem c2 str of
                                        True -> "None"
                                        False -> "Second"
                            False -> case notElem c2 str of
                                        True -> "First"
                                        False -> "Both"

infix1 :: [Int] -> [Int] -> Int
infix1 needle haystack = case isInfixOf needle haystack of
                            True -> 1
                            False -> 42

elemIndex1 :: Int -> [Int] -> Int
elemIndex1 c s
            | pos == (Just 1) = 1
            | pos == (Just 0) = 0 
            | pos == Nothing = -1
            | otherwise = -2
            where pos = elemIndex c s
