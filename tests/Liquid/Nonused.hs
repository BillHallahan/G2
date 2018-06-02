module Nonused where

-- Make sure that, even though the second Int parameter to f is not used,
-- we can find a counterexample to g.

-- Also, important that GHC doesn't inline f into g!

{-@ f :: Int -> {x:Int | x > 0} -> Int @-}
f :: Int -> Int -> Int
f x _ = x

g :: Int
g = f 0 0