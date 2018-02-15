module AddToEven where

{-@ type Even = {v:Int | v mod 2 = 0} @-}

{-@ f :: Even -> Even @-}
f :: Int -> Int
f x = x + g 5

-- Without the below refinement type for g, this file does not verify
-- {-@ g :: Int -> Even @-}
{-@ g :: Int -> Int @-}
g :: Int -> Int
g x = x + x