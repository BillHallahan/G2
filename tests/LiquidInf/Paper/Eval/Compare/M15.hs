{-@ LIQUID "--no-termination" @-}

module M15 (main) where

{-@ main :: { n:Int | n > 0 } -> Int -> { k:Int | k > n } -> { b:Bool | b } @-}
main :: Int -> Int -> Int -> Bool
main n i k = case while cond loop (n, i, k, 0) of
                (_, _, _, j') -> j' >= 0

while :: (a -> Bool) -> (a -> a) -> a -> a
while pred body x = if pred x then while pred body (body x) else x

{-@ cond :: (Int, Int, Int, Int) -> Bool @-}
cond :: (Int, Int, Int, Int) -> Bool
cond (n, i, k, j) = j < n

{-@ loop :: (Int, Int, Int, Int) -> (Int, Int, Int, Int) @-}
loop :: (Int, Int, Int, Int) -> (Int, Int, Int, Int)
loop (n, i, k, j) = (n, i, k - 1, j + 1)