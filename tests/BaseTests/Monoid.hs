module Monoid where

import Data.Monoid

endo1 :: Int -> Int
endo1 x =
    let r = appEndo (Endo (\y -> y + x) <> Endo (\z -> z * z)) 1 in
    case r > 10 of
        True -> r
        False -> -r

sum1 :: Int -> Int
sum1 x =
    let r = getSum (Sum x <> Sum 7) in
    case r > 10 of
        True -> r
        False -> -r
