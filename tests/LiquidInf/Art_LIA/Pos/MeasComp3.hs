module MeasComp where

data W a = W a

{-@ measure extractA @-}
extractA :: W a -> a
extractA (W a) = a

{-@ f :: x:[Int] -> { y:[Int] | len x == len y } @-}
f :: [Int] -> [Int]
f x = g (W (0, x))

{-@ g :: W (Int, [Int]) -> [Int] @-}
g :: W (Int, [Int]) -> [Int]
g (W (_, x)) = x