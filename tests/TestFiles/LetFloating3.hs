module LetFloating3 where

f :: Int -> Int -> Int
f x y = x + g y
    where
        g :: Int -> Int
        g z = 
            let
                h = \q -> q + 1
            in
            z + h z

output19 :: Int -> Int -> Int -> Bool
output19 _ _ = (19 ==)