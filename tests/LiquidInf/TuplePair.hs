module TuplePair where

data TP a = TP a a

{-@ f :: TP ({ x:Int | x > 0}, {y:Int | y < 0 }) -> TP ({ x:Int | x > 0}, {y:Int | y < 0 }) @-}
f :: TP (Int, Int) -> TP (Int, Int)
f = g

g :: TP (Int, Int) -> TP (Int, Int)
g x = x