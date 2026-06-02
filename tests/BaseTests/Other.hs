module Other where

import Data.List

check4VeryEasy2 :: Bool
check4VeryEasy2 = all (0 <=) [0]

callFlip :: Int -> Int -> Bool
callFlip = flip p
    where
        p 0 1 = True
        p _ _ = False