module HeadTest where

{-@ measure myhead @-}
{-@ myhead :: {xs:[a] | len xs > 0} -> a @-}
myhead :: [a] -> a
myhead (x:xs) = x

{-@ f :: xs:[Int] -> {y:Int | len xs > 0 => y = myhead xs} @-}
f :: [Int] -> Int
f (x:xs) = x
f [] = 0