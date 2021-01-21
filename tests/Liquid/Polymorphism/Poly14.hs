module Poly14 (List, initCall) where

data List a = C a

initCall :: Int
initCall = g (f 1)

{-@ f :: k -> (k, Int) @-}
f :: k -> (k, Int)
f k  = (k, 1)

{-@ g :: (k, { x:Int | x > 0 }) -> Int @-}
g :: (k, Int) -> Int
g _ = 1
