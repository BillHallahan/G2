module IO3 where

{-@ f :: IO { b:Bool | b } @-}
f :: IO Bool
f = x

x :: IO Bool
x = return True