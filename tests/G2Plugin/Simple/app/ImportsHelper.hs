module ImportsHelper where

import MyLib

{-# NOINLINE impHelper #-}
impHelper :: Int -> Int
impHelper = otherCall