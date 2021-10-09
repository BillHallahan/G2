{-@ LIQUID "--no-termination" @-}

module M17 (main) where

{-@ main :: Int -> { b:Bool | b } @-}
main :: Int -> Bool
main n = case while cond1 loop1 (n, 1, 1, 0) of
                (n', k', _, _) -> k' >= n'

while :: (a -> Bool) -> (a -> a) -> a -> a
while pred body x = if pred x then while pred body (body x) else x

{-@ cond1 :: (Int, Int, Int, Int) -> Bool @-}
cond1 :: (Int, Int, Int, Int) -> Bool
cond1 (n, k, i, j) = i < n

{-@ loop1 :: (Int, Int, Int, Int) -> (Int, Int, Int, Int) @-}
loop1 :: (Int, Int, Int, Int) -> (Int, Int, Int, Int)
loop1 (n, k, i, j) =
    let
        (n', k', i', j') = while cond2 loop2 (n, k, i, 0)
    in
    (n', k', i' + 1, j')

{-@ cond2 :: (Int, Int, Int, Int) -> Bool @-}
cond2 :: (Int, Int, Int, Int) -> Bool
cond2 (n, k, i, j) = j < i

{-@ loop2 :: (Int, Int, Int, Int) -> (Int, Int, Int, Int) @-}
loop2 :: (Int, Int, Int, Int) -> (Int, Int, Int, Int)
loop2 (n, k, i, j) = (n, k + (i - j), i, j + 1)
