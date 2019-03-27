module SimpleTest where

foo :: Int -> Int
foo x = case x of
    0 -> 3
    _ -> 5
