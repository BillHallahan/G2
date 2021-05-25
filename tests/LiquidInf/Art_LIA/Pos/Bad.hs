module Bad where

{-@ f :: x:Int -> {y:Maybe Int | x == fromJust y} @-}
f :: Int -> Maybe Int
f = Just