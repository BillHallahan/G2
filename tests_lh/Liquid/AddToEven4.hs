module AddToEven2 where

import Prelude hiding (zipWith)

{-@ LIQUID "--no-termination" @-}

{-@ type Even = {v:Int | v mod 2 = 0} @-}

{-@ f :: Even -> Even @-}
f :: Int -> Int
f x = x + g

{-@ g :: {y:Int | y == 1} @-}
g :: Int
g = 2