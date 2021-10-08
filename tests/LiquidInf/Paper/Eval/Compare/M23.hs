{-@ LIQUID "--no-termination" @-}

module M23 (main) where

{-@ main :: { n:Int | n > 0 } -> { b:Bool | b } @-}
main :: Int -> Bool
main n = case while cond loop (n, 0, 0) of
                (n', i', sum') -> sum' >= 0

while :: (a -> Bool) -> (a -> a) -> a -> a
while pred body x = if pred x then while pred body (body x) else x

{-@ cond :: (Int, Int, Int) -> Bool @-}
cond :: (Int, Int, Int) -> Bool
cond (n, i, sum) = i < n

{-@ loop :: (Int, Int, Int) -> (Int, Int, Int) @-}
loop :: (Int, Int, Int) -> (Int, Int, Int)
loop (n, i, sum) = (n, i + 1, sum + i)