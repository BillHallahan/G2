{-@ LIQUID "--no-termination" @-}

module Test51 (main) where

data Peano = Succ | Nil

{-@ main :: Bool -> { b : Bool | b } @-}
main :: Bool -> Bool
main xs = case while xs loop (1, 0, 0, 0) of
                (w', z', x', y') -> x' <= 1

while :: Bool -> (a -> a) -> a -> a
while ys body x = if ys then while False body (body x) else x

{-@ loop :: (Int, Int, Int, Int) -> (Int, Int, Int, Int) @-}
loop :: (Int, Int, Int, Int) -> (Int, Int, Int, Int)
loop (w, z, x, y) =
    ( if w `mod` 2 == 1 then w + 1 else w
    , if z `mod` 2 == 0 then z + 1 else z
    , if w `mod` 2 == 1 then x + 1 else x
    , if z `mod` 2 == 0 then y + 1 else y)
