module Data where

-- {-@ data R = R Nat @-}
data R = R Int

{-@ f :: { x:Int | x > 0 } -> { y:Int | y > 0 } @-}
f :: Int -> Int
f x = case R x of
			R y -> y + 1
