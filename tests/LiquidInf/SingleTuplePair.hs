module SingleTuplePair where

data STP a = STP a (a, a)

{-@ f :: STP { x:Int | x > 0 } -> STP { x:Int | x > 0 } @-}
f :: STP Int -> STP Int
f = g

g :: STP Int -> STP Int
g x = x