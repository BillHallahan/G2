{-@ LIQUID "--no-termination" @-}

module M19 (main) where

{-@ main :: Bool -> { b:Bool | b } @-}
main :: Bool -> Bool
main flag =
    case while cond loop (flag, 0, 0) of
        (_, _, j) -> if flag then j == 100 else True

while :: (a -> Bool) -> (a -> a) -> a -> a
while pred body x = if pred x then while pred body (body x) else x

{-@ cond :: (Bool, Int, Int) -> Bool @-}
cond :: (Bool, Int, Int) -> Bool
cond (_, b, j) = b < 100

{-@ loop :: (Bool, Int, Int) -> (Bool, Int, Int) @-}
loop :: (Bool, Int, Int) -> (Bool, Int, Int)
loop (flag, b, j) = if flag then (flag, b + 1, j + 1) else (flag, b + 1, j)