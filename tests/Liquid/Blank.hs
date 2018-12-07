module Blank () where

-- this is simply, a blank file.

negg :: Int -> Int 
negg x = 0 - x

twice :: (a -> a) -> a -> a 
twice f x = f (f x)

{-@ test :: Nat -> Nat @-}
test :: Int -> Int 
test n = twice negg n