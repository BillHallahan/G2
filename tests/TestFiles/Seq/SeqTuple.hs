{-# LANGUAGE CPP, MultiWayIf #-}

module Seq1 where

import Data.List

con :: Int -> [(Int, Int)] -> [(Int, Int)] -> [(Int, Int)]
con x xs ys = if x > 10 then xs ++ ys else ys ++ xs

listLen :: [(Int, Int)] -> (Int, Bool)
listLen xs = let l = length xs in (l, case l > 5 of True -> False; False -> True)
