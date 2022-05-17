module Chr where

import Data.Char

lowerLetters :: [Char]
lowerLetters = map chr [97..97 + 25]

allLetters :: [Char]
allLetters = map chr $ [65..65 + 25] ++ [97..97 + 25]

lowerLetterCodes :: [Int]
lowerLetterCodes = map ord ['a'..'z']

printBasedOnChr :: Int -> Int
printBasedOnChr x
    | chr x == 'A' = x
    | chr x == 'B' = x + x
    | chr x == 'C' = x + x + x
    | chr x == 'D' = x + x + x + x
    | chr x == 'E' = x + x + x + x + x
    | chr x == 'F' = x + x + x + x + x + x
    | chr x == 'G' = x + x + x + x + x + x + x
    | otherwise = -1

printBasedOnOrd :: Char -> String
printBasedOnOrd x
    | ord x == 65 = [x]
    | ord x == 66 = [x, x]
    | ord x == 67 = [x, x, x]
    | ord x == 68 = [x, x, x, x]
    | ord x == 69 = [x, x, x, x, x]
    | ord x == 70 = [x, x, x, x, x, x]
    | ord x == 71 = [x, x, x, x, x, x, x]
    | otherwise = ""
