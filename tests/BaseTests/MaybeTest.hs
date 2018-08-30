module MaybeTest where

import Data.List
import Data.Maybe

-- averageF :: [Float] -> Float
-- averageF xs = sumN xs / lengthF xs

head :: [a] -> a
head (x:xs) = x
head _ = error "head"

sumN :: Num a => [a] -> a
sumN (x:xs) = x + sumN xs
sumN _ = 0

lengthN :: Num b => [a] -> b
lengthN (_:xs) = 1 + lengthN xs
lengthN _ = 0

average :: (Real a, Fractional a) => [a] -> a
average xs = sum xs / genericLength xs

averageF :: [Float] -> Float
averageF xs = sum xs / genericLength xs

maybeAvg :: Fractional a => [Maybe a] -> a
maybeAvg xs = sum (catMaybes xs) / genericLength xs



average' :: (Real a, Fractional a) => [a] -> a
average' xs = sumN xs / lengthN xs