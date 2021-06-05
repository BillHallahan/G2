module Poly10 where

data C a = C a (Int -> a) 

{-@ prop :: { r:Int | r == 0 } @-}
prop :: Int
prop = higher_order func

higher_order :: C a -> a
higher_order (C _ f) = f 0

func :: C Int
func = C 0 (\_ -> 0) 

t :: Int -> Int
t _ = 1