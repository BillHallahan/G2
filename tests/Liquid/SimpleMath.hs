module SimpleMath where

{-@ type Pos = {v:Int | 0 < v} @-}

{-@ abs2 :: Int -> Pos @-}
abs2 :: Int -> Int
abs2 x
	| x > 0 = x
	| otherwise = -x

{-@ add :: x:Int -> y:Int -> {z:Int | x <= z && y <= z}@-}
add :: Int -> Int -> Int
add = (+)