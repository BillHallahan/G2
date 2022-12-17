module Poly8 where

{-@ prop :: { r:Int | r == 0 } @-}
prop :: Int
prop = higher_order func

higher_order :: (Int -> a) -> a
higher_order f = f 0

func :: Int -> Int
func _ = 0 