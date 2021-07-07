module IO1 where

{-@ f :: IO { x:Int | x == 2 } @-}
f :: IO Int
f = return x

x :: Int
x = 2