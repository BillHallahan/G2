{-@ LIQUID "--no-termination" @-}

module M19 (main) where

{-@ main :: { n:Int | n >= 0 } -> { m:Int | m >= 0 && m < n } -> { b:Bool | b } @-}
main :: Int -> Int -> Bool
main n m =
    case while (cond n m) (loop n m) (0, m) of
        (_, y') -> n == y'

while :: (a -> Bool) -> (a -> a) -> a -> a
while pred body x = if pred x then while pred body (body x) else x

{-@ cond :: Int -> Int -> (Int, Int) -> Bool @-}
cond :: Int -> Int -> (Int, Int) -> Bool
cond n m (x, y) = x < n

{-@ loop :: Int -> Int -> (Int, Int) -> (Int, Int) @-}
loop :: Int -> Int -> (Int, Int) -> (Int, Int)
loop n m (x, y) = (x + 1, if x + 1 > m then y + 1 else y)