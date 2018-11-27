module Where1 where

f :: Int -> Int
f x = g x
    where
        g :: Int -> Int
        g 4 = 1
        g y = g 4
