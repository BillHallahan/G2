module Poly8 where

{-@ prop :: (Int -> Int) -> { r:Int | r == 0 } @-}
prop :: (Int -> Int) -> Int
prop = higher_order

higher_order :: (Int -> a) -> a
higher_order f = f 0