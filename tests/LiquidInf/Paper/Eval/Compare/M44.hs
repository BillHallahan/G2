{-@ LIQUID "--no-termination" @-}

module M44 (main) where

{-@ main :: Int -> Int -> { b:Bool | b } @-}
main :: Int -> Int -> Bool
main k flag = case while cond loop (k, flag, 0, 0, if flag == 1 then 1 else 2) of
                (k', flag', i', j', n') -> if flag == 1 then j' == i' else True

while :: (a -> Bool) -> (a -> a) -> a -> a
while pred body x = if pred x then while pred body (body x) else x

{-@ cond :: (Int, Int, Int, Int, Int) -> Bool @-}
cond :: (Int, Int, Int, Int, Int) -> Bool
cond (k, flag, i, j, n) = i <= k

{-@ loop :: (Int, Int, Int, Int, Int) -> (Int, Int, Int, Int, Int) @-}
loop :: (Int, Int, Int, Int, Int) -> (Int, Int, Int, Int, Int)
loop (k, flag, i, j, n) = (k, flag, i + 1, j + n, n)
