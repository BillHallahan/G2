module Kadane where

import G2.Plugin

{-# ANN module ("--smt-tuples --smt z3,cvc5") #-}

{-# ANN total (SMTEquivIs "totalSmt") #-}
total :: [Int] -> Int
total [] = 0
total (x:xs) = x + total xs

totalSmt :: [Int] -> Int
totalSmt xs = smtFoldLeft (\acc y -> acc + y) 0 xs

{-# ANN kadane (SMTEquivIs "kadaneSmt") #-}
kadane :: [Int] -> Int
kadane xs = kadLoop xs 0 0

kadaneSmt :: [Int] -> Int
kadaneSmt xs = kadLoopSmt xs 0 0

{-# ANN kadLoop (SMTEquivIs "kadLoopSmt") #-}
kadLoop :: [Int] -> Int -> Int -> Int
kadLoop [] _ best = best
kadLoop (y:ys) cur best = kadLoop ys (max y (cur + y)) (max best (max y (cur + y)))

kadLoopSmt :: [Int] -> Int -> Int -> Int
kadLoopSmt xs cur best =
    let f (cur', best') y = (max y (cur' + y), max best' (max y (cur' + y)))
        (res, _) = (smtFoldLeft f (cur, best) xs)
    in res

{-# ANN propKadaneNil Prop #-}
propKadaneNil :: Bool
propKadaneNil = kadane [] == 0

-- Empty subarrays are allowed, so this works
{-# ANN propKadaneNonNeg Prop #-}
propKadaneNonNeg :: [Int] -> Bool
propKadaneNonNeg xs = kadane xs >= 0

{-# ANN propKadaneGeTotal Prop #-}
propKadaneGeTotal :: [Int] -> Bool
propKadaneGeTotal xs = kadane xs >= total xs
