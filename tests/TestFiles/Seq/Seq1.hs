{-# LANGUAGE CPP, MultiWayIf #-}

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
listApp xs ys = let cs = xs ++ ys in
                if | cs == [1, 2, 3, 4, 5, 6, 7, 8, 9] -> 2
                   | cs == [9, 8, 7, 6, 5, 4] -> 1
                   | otherwise -> 0

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

-- ...

delete1 :: Integer -> [Integer] -> (Int, [Integer])
delete1 c s
    | length s < 3 = (1, d)
    | length d < length s = (2, d)
    | otherwise = (3, d)
    where
        d = delete c s

stripPrefix1 :: [Int] -> [Int] -> Maybe [Int]
stripPrefix1 = stripPrefix

stripPrefix2 :: [Int] -> [Int] -> (Int, Maybe [Int])
stripPrefix2 xs ys
    | Just zs <- m_zs, length zs > 3 = (1, m_zs)
    | Just zs <- m_zs, 2 < length xs - length zs = (2, m_zs)
    | Nothing <- m_zs = (3, m_zs)
    | length xs > 0 = (4, m_zs)
    | otherwise = (5, m_zs)
    where
        m_zs = stripPrefix xs ys

genericLength1 :: [Int] -> (Integer, Char)
genericLength1 xs
    | ln < 4 = (ln, 'X')
    | ln > 15 = (ln, 'L')
    | ln == 7 = (ln, 'Q')
    | otherwise = (42, 'A')
    where
        ln = genericLength xs

genericTake1 :: [Int] -> Integer -> (Maybe String, Int)
genericTake1 xs n
    | took == [1, 2, 3, 4, 5] = (Nothing, 0)
    | took == [3, 4, 5] = (Just "Yes", 1)
    | length took > 10 = (Just "Long", 2)
    | otherwise = (Nothing, 3)
    where
        took = genericTake n xs

genericDrop1 :: [Int] -> Integer -> (Integer, String)
genericDrop1 xs n
    | dropped == [10, 9, 4] = (n, "DD")
    | length dropped < 2 = (-1, "Short")
    | otherwise = (n, xs)
    where
        dropped = genericDrop n xs

genericSplitAt1 :: [Int] -> Integer -> ([Int], Bool)
genericSplitAt1 xs n
    | length start > length end = (start, True)
    | start == end = (start, False)
    | start == [4, 7, 8] = (start, True)
    | otherwise = ("Okay", False)
    where
        (start, end) = genericSplitAt n xs

-- Note that there should be an fourth case here due to an invalid index error
genericIndex1 :: [Int] -> Integer -> (Int, Int)
genericIndex1 xs n
    | chr == 'Z' = (chr, 0)
    | chr < 'Q' = (chr, 1)
    | otherwise = (chr, 2)
    where
        chr = xs `genericIndex` (n + 1)

-- This doesn't lessen outputs, it only tests whether genericReplicate works with SMT Strings
genericReplicate1 :: Integer -> Int -> ([Int], Int)
genericReplicate1 n c
    | length rs > 7 = (rs, 1)
    | otherwise = (rs, 2)
    where
        rs = genericReplicate n c

isPrefixOf1 :: [Float] -> [Float] -> (Int, Bool)
isPrefixOf1 s1 s2
    | length s1 < 3 = (1, p)
    | length s2 < 3 = (2, p)
    | length s1 + 3 < length s2, p = (3, p)
    | p = (4, p)
    | length s1 + 3 < length s2 = (5, p)
    | otherwise = (6, p)
    where
        p = isPrefixOf s1 s2

isSuffixOf1Int :: [Int] -> [Int] -> (Int, Bool)
isSuffixOf1Int s1 s2
    | length s1 < 3 = (1, p)
    | length s2 < 3 = (2, p)
    | length s1 + 3 < length s2, p = (3, p)
    | p = (4, p)
    | length s1 + 3 < length s2 = (5, p)
    | otherwise = (6, p)
    where
        p = isSuffixOf s1 s2

isSuffixOf1Double :: [Double] -> [Double] -> (Int, Bool)
isSuffixOf1Double s1 s2
    | length s1 < 3 = (1, p)
    | length s2 < 3 = (2, p)
    | length s1 + 3 < length s2, p = (3, p)
    | p = (4, p)
    | length s1 + 3 < length s2 = (5, p)
    | otherwise = (6, p)
    where
        p = isSuffixOf s1 s2

#if MIN_VERSION_base(4,19,0)
unsnoc1 :: [Int] -> Maybe Int
unsnoc1 xs
    | Just (s, e) <- uc, s == [1, 2, 3] = Just 0
    | Nothing == uc = Just 1
    | Just (s, e) <- uc, length s == 0 = Just 2
    | otherwise = Nothing
    where
        uc = unsnoc xs

unsnoc2 :: [Int] -> Maybe ([Int], Int)
unsnoc2 = unsnoc

totalIndex1 :: [Int] -> [Maybe Int]
totalIndex1 xs = [xs !? (-1), xs !? 0, xs !? 15]
#endif

