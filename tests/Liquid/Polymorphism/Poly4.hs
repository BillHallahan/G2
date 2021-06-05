module Poly4 where

data C a = C a

{-@ f :: (C { x:Int | x > 0 }) -> (C { x:Int | x > 0 }) @-}
f :: C Int -> C Int
f x = g x

g :: C a -> C a
g x = x