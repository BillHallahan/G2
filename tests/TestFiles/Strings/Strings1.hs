{-# LANGUAGE CPP #-}

module Strings1 where

import Data.List

con :: String -> String -> String
con xs ys = xs ++ ys

eq :: String -> String -> Bool
eq xs ys = xs == ys

eqGt1 :: String -> String -> Bool
eqGt1 xs ys = xs == ys && length xs >= 1

capABC :: String -> String
capABC ('a':xs) = 'A':capABC xs
capABC ('b':xs) = 'B':capABC xs
capABC ('c':xs) = 'C':capABC xs
capABC (x:xs) = x:capABC xs
capABC "" = ""

appendEq :: String -> String
appendEq s = s ++ "!"

exclaimEq :: String -> String -> Bool
exclaimEq s1 s2 = s1 == s2 ++ "!"

stringSub1 :: String -> Bool
stringSub1 (_:_:_:_) = False
stringSub1 str = any (`elem` str) "~`!@#$%^&*-_+="

stringSub2 :: String -> Bool
stringSub2 (_:_:_:_) = False
stringSub2 str = any (`elem` str) "{}|:;<>?/,."

stringSub3 :: String -> Bool
stringSub3 (_:_:_:_) = False
stringSub3 str = any (`elem` str) "()\"\'"

stringSub4 :: String -> Bool
stringSub4 (_:_:_:_) = False
stringSub4 str = any (`elem` str) "\\"

nStringSub3 :: String -> String
nStringSub3 s = if stringSub3 s then "\n" ++ s else s

nStringSub4 :: String -> String
nStringSub4 s = if stringSub4 s then "\n" ++ s else s

strLen :: String -> (Int, Bool)
strLen xs = let l = length xs in (l, case l > 5 of True -> False; False -> True)

strApp :: String -> String -> Int
strApp xs ys = case xs ++ ys of
                    "Hello World!" -> 2
                    "Goodbye" -> 1
                    _ -> 0

con2 :: String -> String -> (String, Int)
con2 xs ys = case xs ++ ys of
    xs@(_:_:_) -> (xs, 3)
    xs@(_:_) -> (xs, 2)
    [] -> ([], 1)

strIndex :: String -> (Bool, String)
strIndex str =
    case str !! 50 of
        '3' -> (True, "Three")
        '2' -> (False, "Two")
        _ -> (False, "None")

taker1 :: String -> (Bool, String)
taker1 str = case take 30 str of
                x@"HelloHelloHelloHelloHelloHello" -> (True, x)
                y -> (False, y)

taker2 :: String -> (Bool, String)
taker2 str = case take 22 str of
                x@"Hi" -> (True, x)
                y -> (False, y)

conTaker1 :: String -> String -> (Int, String)
conTaker1 xs ys =
    case take 18 xs ++ take 18 ys of
        zs@"It was a dark and stormy night" | length xs < length ys -> (1, zs)
                                            | length xs > 18 -> (2, zs)
                                            | otherwise -> (3, zs)
        zs -> (4, zs)

conTaker2 :: String -> String -> (Int, String)
conTaker2 xs ys =
    case take 10 (xs ++ ys) of
        zs@"HelloHello" -> (1, zs)
        zs -> (2, zs)

lengthCon1 :: String -> (Int, Bool)
lengthCon1 xs = let z = length (xs ++ "!!!") in (z, case z > 5 of True -> False; False -> True)

conIndex1 :: Int -> String -> (Int, Char)
conIndex1 n xs | 10 <= n, n < 20, length xs > 10 = (n, (xs ++ xs) !! n)
               | otherwise = (n, (xs ++ xs) !! n)

-- For smt strings, needs a fairly long string for speedup here
eq1 :: String -> Int
eq1 s = case "123456789019234623479629031641906590659651902651908560189893412572348901572902834752389057389057890345789037529803" == s of
            True -> 1
            _ -> 0

eq2 :: String -> Int
eq2 s = case s of
            "123456789019234623479629031641906590659651902651908560189893412572348901572902834752389057389057890345789037529803" -> 1
            _ -> 0

eq3 :: String -> String -> Int
eq3 s1 s2 = case "123456789 123456789 123456789" == s1 ++ s2 of
                        True -> 1
                        False -> 0

init1 :: String -> (Int, String)
init1 xs | length xs < 20 = (1, init xs)
         | length xs < 40 = (2, init xs)
         | otherwise = (3, init xs)

null1 :: String -> Int
null1 xs =
    case null xs of
        True -> case null (xs ++ xs) of
                    True -> 1
                    False -> error "Impossible"
        False -> 2

last1 :: String -> (Int, Char)
last1 xs | length xs > 50 = (1, last xs)
         | length xs > 30 = (2, last xs)
         | otherwise = (3, last xs)

drop1 :: String -> (Bool, String)
drop1 str = case drop 50 str of
                x@"HelloHelloHelloHelloHelloHello" -> (True, x)
                y -> (False, y)

drop2 :: String -> (Bool, String)
drop2 str = case drop 22 str of
                x@"Hi" -> (True, x)
                y -> (False, y)

drop3 :: String -> Int
drop3 str = case drop 20 str of
                "" | length str /= 20 -> 1
                   | str /= "" -> 2
                _ -> 3

elem1 :: String -> Char -> (Bool, String)
elem1 str ch = case elem ch str of
                    True -> (False, "Switched")
                    False -> (True, "Opposite Day!")

notElem1 :: String -> Char -> Char -> String
notElem1 str c1 c2 = case notElem c1 str of
                            True -> case notElem c2 str of
                                        True -> "None"
                                        False -> "Second"
                            False -> case notElem c2 str of
                                        True -> "First"
                                        False -> "Both"

infix1 :: String -> String -> Int
infix1 needle haystack = case isInfixOf needle haystack of
                            True -> 1
                            False -> 42

elemIndex1 :: Char -> String -> Int
elemIndex1 c s
            | pos == (Just 1) = 1
            | pos == (Just 0) = 0 
            | pos == Nothing = -1
            | otherwise = -2
            where pos = elemIndex c s

strGt :: String -> String -> Int
strGt x y | length x < 2 = 1
          | length y < 2 = 2
          | x > y = 3
          | otherwise = 4

strGe :: String -> String -> Int
strGe x y | length x < 2 = 1
          | length y < 2 = 2
          | x > y = 3
          | x >= y = 4
          | otherwise = 5

strLt :: String -> String -> Int
strLt x y | length x < 2 = 1
          | length y < 2 = 2
          | x < y = 3
          | otherwise = 4

strLe :: String -> String -> Int
strLe x y | length x < 2 = 1
          | length y < 2 = 2
          | x < y = 3
          | x <= y = 4
          | otherwise = 5

compare1 :: String -> String -> Int
compare1 x y | length x < 2 = 1
             | length y < 2 = 2
             | EQ <- c = 3
             | LT <- c = 4
             | GT <- c = 5
             where c = compare x y

max1 :: String -> String -> String
max1 = max

max2 :: String -> String -> (Int, String)
max2 x y | length x < 2 = (1, max x y)
         | length y < 2 = (2, max x y)
         | x == y = (3, max x y)
         | otherwise = (4, max x y)

min1 :: String -> String -> String
min1 = min

min2 :: String -> String -> (Int, String)
min2 x y | length x < 2 = (1, min x y)
         | length y < 2 = (2, min x y)
         | x == y = (3, min x y)
         | otherwise = (4, min x y)

delete1 :: Char -> String -> (Int, String)
delete1 c s
    | length s < 3 = (1, d)
    | length d < length s = (2, d)
    | otherwise = (3, d)
    where
        d = delete c s

stripPrefix1 :: String -> String -> Maybe String
stripPrefix1 = stripPrefix

stripPrefix2 :: String -> String -> (Int, Maybe String)
stripPrefix2 xs ys
    | Just zs <- m_zs, length zs > 3 = (1, m_zs)
    | Just zs <- m_zs, 2 < length xs - length zs = (2, m_zs)
    | Nothing <- m_zs = (3, m_zs)
    | length xs > 0 = (4, m_zs)
    | otherwise = (5, m_zs)
    where
        m_zs = stripPrefix xs ys

genericLength1 :: String -> (Integer, Char)
genericLength1 xs
    | ln < 4 = (ln, 'X')
    | ln > 15 = (ln, 'L')
    | ln == 7 = (ln, 'Q')
    | otherwise = (42, 'A')
    where
        ln = genericLength xs

genericTake1 :: String -> Integer -> (Maybe String, Int)
genericTake1 xs n
    | took == "Hi" = (Nothing, 0)
    | took == "Bye" = (Just "Yes", 1)
    | length took > 10 = (Just "Long", 2)
    | otherwise = (Nothing, 3)
    where
        took = genericTake n xs

genericDrop1 :: String -> Integer -> (Integer, String)
genericDrop1 xs n
    | dropped == "Drop" = (n, "DD")
    | length dropped < 2 = (-1, "Short")
    | otherwise = (n, xs)
    where
        dropped = genericDrop n xs

genericSplitAt1 :: String -> Integer -> (String, Bool)
genericSplitAt1 xs n
    | length start > length end = (start, True)
    | start == end = ("Same", False)
    | start == "Hello" = ("Hello World!", True)
    | otherwise = ("Okay", False)
    where
        (start, end) = genericSplitAt n xs

-- Note that there should be an fourth case here due to an invalid index error
genericIndex1 :: String -> Integer -> (Char, Int)
genericIndex1 xs n
    | chr == 'Z' = (chr, 0)
    | chr < 'Q' = (chr, 1)
    | otherwise = ('!', 2)
    where
        chr = xs `genericIndex` (n + 1)

-- This doesn't lessen outputs, it only tests whether genericReplicate works with SMT Strings
genericReplicate1 :: Integer -> Char -> String
genericReplicate1 = genericReplicate

-- This usually hits the solver outputting a delete character
bigString :: String -> Int
bigString s = case length s > 100 of
                True -> 0
                False -> 1

isPrefixOf1 :: String -> String -> (Int, Bool)
isPrefixOf1 s1 s2
    | length s1 < 3 = (1, p)
    | length s2 < 3 = (2, p)
    | length s1 + 3 < length s2, p = (3, p)
    | p = (4, p)
    | length s1 + 3 < length s2 = (5, p)
    | otherwise = (6, p)
    where
        p = isPrefixOf s1 s2

isSuffixOf1 :: String -> String -> (Int, Bool)
isSuffixOf1 s1 s2
    | length s1 < 3 = (1, p)
    | length s2 < 3 = (2, p)
    | length s1 + 3 < length s2, p = (3, p)
    | p = (4, p)
    | length s1 + 3 < length s2 = (5, p)
    | otherwise = (6, p)
    where
        p = isSuffixOf s1 s2

#if MIN_VERSION_base(4,19,0)
unsnoc1 :: String -> Maybe Int
unsnoc1 xs
    | Just (s, e) <- uc, s == "Hello" = Just 0
    | Nothing == uc = Just 1
    | Just (s, e) <- uc, length s == 0 = Just 2
    | otherwise = Nothing
    where
        uc = unsnoc xs

unsnoc2 :: String -> Maybe (String, Char)
unsnoc2 = unsnoc

totalIndex1 :: String -> [Maybe Char]
totalIndex1 xs = [xs !? (-1), xs !? 0, xs !? 15]
#endif

splitAt1 :: String -> Maybe (String, Int)
splitAt1 xs
    | a == b = Just (a, 0)
    | length a < 4 = Just (b, 1)
    | b == (a ++ a) = Just (b, 2)
    | otherwise = Nothing
    where
        (a, b) = splitAt 10 xs

notEq1 :: String -> Int
notEq1 s = case s /= "verylongstringverylongstringVERYLONGSTRINGVERYLONGSTRING" of
                True -> 4
                False -> 2
