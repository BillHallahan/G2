module MaybeTest where

import Data.List
import Data.Maybe

-- averageF :: [Float] -> Float
-- averageF xs = sumN xs / lengthF xs

sumN :: Num a => [a] -> a
sumN xss =
    case xss of
        x:xs -> x + sumN xs
        _ -> 0

lengthN :: Num b => [a] -> b
lengthN xss =
    case xss of
        _:xs -> 1 + lengthN xs
        _ -> 0

average :: (Real a, Fractional a) => [a] -> a
average xs = sum xs / genericLength xs

averageF :: [Float] -> Float
averageF xs = sum xs / genericLength xs

maybeAvg :: Fractional a => [Maybe a] -> a
maybeAvg xs = sum (catMaybes xs) / genericLength xs
