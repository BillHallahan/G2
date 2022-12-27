module IO1 where

{-@ f :: IO Int @-}
f :: IO Int
f = return g

g :: Int
g = 1