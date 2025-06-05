module Strings1 where

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

