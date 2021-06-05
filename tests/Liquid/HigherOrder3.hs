{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

module Combined () where

{-@ m :: (Int -> Int) -> { ys:Int | false } @-}
m :: (Int -> Int) -> Int
m f = f 1