module NestedLength where

{-@ nested :: xs:[Int] -> [{ y:Int | len xs > 0 }] @-}
nested :: [Int] -> [Int]
nested xs = xs