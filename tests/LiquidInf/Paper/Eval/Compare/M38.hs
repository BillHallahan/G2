{-@ LIQUID "--no-termination" @-}

module M38 (main) where

{-@ main :: { n:Int | n >= 0 } -> { b:Bool | b } @-}
main :: Int -> Bool
main n =
    case while cond loop (n, 0, 0, 0) of
        (n', x', y', i') -> if i' `mod` 2 == 0 then x' == 2 * y' else True

while :: (a -> Bool) -> (a -> a) -> a -> a
while pred body x = if pred x then while pred body (body x) else x

{-@ cond :: (Int, Int, Int, Int) -> Bool @-}
cond :: (Int, Int, Int, Int) -> Bool
cond  (n, x, y, i) = i < n

{-@ loop :: (Int, Int, Int, Int) -> (Int, Int, Int, Int) @-}
loop :: (Int, Int, Int, Int) -> (Int, Int, Int, Int)
loop (n, x, y, i) = (n, x + 1, if (i + 1) `mod` 2 == 0 then y + 1 else y, i + 1)