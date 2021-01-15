module Poly9 where

data C a = C (Int -> a) 

{-@ prop :: { r:Int | r == 0 } @-}
prop :: Int
prop = higher_order func

higher_order :: C a -> a
higher_order (C f) = f 0

func :: C Int
func = C (\_ -> 0) 