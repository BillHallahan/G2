module Trivial where

{-@ f :: Int -> Int @-}
f :: Int -> Int 
f 0 = 0
f _ = die 0

{-@ die :: {x:Int | false} -> a @-}
die :: Int -> a
die x = error "die"
