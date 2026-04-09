module FDef where

import G2.Plugin

import Helper
import MyLib

{-# ANN f SymEx #-}
f :: MyInt -> Int -> Int
f (MyInt x) y = call (MyInt y) + helper x + 1
f (MyIntAlso x) y = call (MyIntAlso y) + x + x + 1

{-# ANN g SymEx #-}
g :: MyInt -> Int -> Int
g (MyInt _) _ = 1
g (MyIntAlso _) _ = 2

{-# ANN recCall (SymExWithConfig "--n 14000") #-}
recCall :: Int -> Int
recCall = r 40

r :: Int -> Int -> Int
r n x | n < 0 = x
      | otherwise = r (n - 1) (n + x) 