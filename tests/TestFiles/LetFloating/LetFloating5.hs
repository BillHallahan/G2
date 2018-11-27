module LetFloating4 where

f :: Int -> Int -> Int
f x y = x + g y
    where
        {-# NOINLINE g #-}
        g :: Int -> Int
        g z = 
            let
                {-# NOINLINE h #-}
                h = \q -> q + 1
            in
            z + h z

output19 :: Int -> Int -> Int -> Bool
output19 _ _ = (19 ==)
