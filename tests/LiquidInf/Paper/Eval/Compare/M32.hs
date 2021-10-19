{-@ LIQUID "--no-termination" @-}

module M32 (main) where

{-@ main :: Bool -> Int -> { b:Bool | b } @-}
main :: Bool -> Int -> Bool
main b ij = case while 100 (b, ij, ij, 0) of
                (b', i, j, n) -> i == j

{-@ while :: Int -> (Bool, Int, Int, Int) -> (Bool, Int, Int, Int) @-}
while :: Int -> (Bool, Int, Int, Int) -> (Bool, Int, Int, Int)
while k (b, i, j, n) =
    if n < 2 * k
        then while k (not b, if b then i + 1 else i, if not b then j + 1 else j, n + 1)
        else (b, i, j, n)