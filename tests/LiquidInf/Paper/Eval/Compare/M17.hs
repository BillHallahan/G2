{-@ LIQUID "--no-termination" @-}

module M17 (main) where

{-@ main :: Int -> { b:Bool | b } @-}
main :: Int -> Bool
main n = case while1 n (1, 1, 0) of
                (k', _, _) -> k' >= n

while1 :: Int -> (Int, Int, Int) -> (Int, Int, Int)
while1 n (k, i, j) = if i < n
                        then (let
                                (k', i', j') = while2 n (k, i, 0)
                              in
                              while1 n (k', i' + 1, j'))
                        else (k, i, j)

{-@ while2 :: Int -> (Int, Int, Int) -> (Int, Int, Int) @-}
while2 :: Int -> (Int, Int, Int) -> (Int, Int, Int)
while2 n (k, i, j) = if j < i
                        then while2 n (k + (i - j), i, j + 1)
                        else (k, i, j)