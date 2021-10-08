{-@ LIQUID "--no-termination" @-}

module M34 (main) where

{-@ main :: { n:Int | n >= 0 } -> { b:Bool | b } @-}
main :: Int -> Bool
main n =
    case while (cond n 10) (loop n 10) (0, 0, 0) of
        (i', x', y') -> if i' == 10 then x' == 2 * y' else True

while :: (a -> Bool) -> (a -> a) -> a -> a
while pred body x = if pred x then while pred body (body x) else x

{-@ cond :: Int -> Int -> (Int, Int, Int) -> Bool @-}
cond :: Int -> Int -> (Int, Int, Int) -> Bool
cond n m (i, x, y) = i < n

{-@ loop :: Int -> Int -> (Int, Int, Int) -> (Int, Int, Int) @-}
loop :: Int -> Int -> (Int, Int, Int) -> (Int, Int, Int)
loop n m (i, x, y) = (i + 1, x + 1, if (i + 1) `mod` 2 == 0 then y + 1 else y)