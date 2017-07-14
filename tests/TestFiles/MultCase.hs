module MultCase where

f :: Double -> Bool
f x = case x * 2 of
            4 -> True
            2 -> False
            otherwise -> False