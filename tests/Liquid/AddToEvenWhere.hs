module AddToEvenWhere where

import Prelude hiding (zipWith)

{-@ type Even = {v:Int | v mod 2 = 0} @-}

{-@ f :: Even -> Even @-}
f :: Int -> Int
f x = x + g x
    where
        g :: Int -> Int
        g x = if x > 0 then x + x else g (x + 2)