module SimpleAnnot where

f :: Int -> Int
f b = b + 1

{-@ simpleF :: x:Nat -> { y:Int | y > 0} @-}
simpleF :: Int -> Int
simpleF x = f x

{-@ simpleG :: { x:Int | x > 0} -> { y:Int | y > 0} @-}
simpleG :: Int -> Int
simpleG x = f x
