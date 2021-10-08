{-@ LIQUID "--no-termination" @-}

module M23 (main) where

{-@ main :: Bool -> Int -> { b:Bool | b } @-}
main :: Bool -> Int -> Bool
main b ij = case while cond loop (100, b, ij, ij, 0) of
                (k, b', i, j, n) -> i == j

while :: (a -> Bool) -> (a -> a) -> a -> a
while pred body x = if pred x then while pred body (body x) else x

{-@ cond :: (Int, Bool, Int, Int, Int) -> Bool @-}
cond :: (Int, Bool, Int, Int, Int) -> Bool
cond (k, _, _, _, n) = n < 2 * k

{-@ loop :: (Int, Bool, Int, Int, Int) -> (Int, Bool, Int, Int, Int) @-}
loop :: (Int, Bool, Int, Int, Int) -> (Int, Bool, Int, Int, Int)
loop (k, b, i, j, n) = (k, not b, if b then i + 1 else i, if not b then j + 1 else j, n + 1)