{-@ LIQUID "--no-termination" @-}

module M35 (main) where

{-@ main :: Int -> { b:Bool | b } @-}
main :: Int -> Bool
main n = case while cond loop (n, 0) of
                (n', x) -> if n' > 0 then x == n' else True

while :: (a -> Bool) -> (a -> a) -> a -> a
while pred body x = if pred x then while pred body (body x) else x

{-@ cond :: (Int, Int) -> Bool @-}
cond :: (Int, Int) -> Bool
cond (n, x) = x < n

{-@ loop :: (Int, Int) -> (Int, Int) @-}
loop :: (Int, Int) -> (Int, Int)
loop (n, x) = (n, x + 1)