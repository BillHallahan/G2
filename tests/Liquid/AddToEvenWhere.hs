module AddToEvenWhere where

import Prelude hiding (zipWith)

{-@ LIQUID "--no-termination" @-}

{-@ type Even = {v:Int | v mod 2 = 0} @-}

{-@ f :: Even -> Even @-}
f :: Int -> Int
f x = x + g 5
    where
        g :: Int -> Int
        g x = x + x
