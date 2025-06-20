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
