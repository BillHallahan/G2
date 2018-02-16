module AddToEven where

{-@ type Even = {v:Int | v mod 2 = 0} @-}

{-@ f :: Even -> Even @-}
f :: Int -> Int
f x = x + g 5

-- Without the below refinement type for g, this file can not be verified
-- {-@ g :: Int -> Even @-}
-- {-@ g :: Int -> {v:Int | v /= -1} @-}
g :: Int -> Int
g x = x + x