-- cmd_line = (--no-keep_quals)

module AddToEven () where

import Prelude hiding (zipWith)

{-@ LIQUID "--no-termination" @-}

{-@ type Even = {v:Int | v mod 2 = 0} @-}

{-@ f :: Even -> Even @-}
f :: Int -> Int
f x = x + g x

g :: Int -> Int
g x = h x

h :: Int -> Int
h x = 4 * x