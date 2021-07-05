module IO2 where

{-@ f :: Int -> IO { x:Int | x == 2 } @-}
f :: Int -> IO Int
f _ = return g

g :: Int
g = 1