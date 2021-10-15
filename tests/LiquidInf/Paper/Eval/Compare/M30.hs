{-@ LIQUID "--no-termination" @-}

module M30 (main) where

{-@ main :: { b:Bool | b } @-}
main :: Bool
main = case while cond loop (0, 0) of
                (i', c') -> c' >= 0

while :: (a -> Bool) -> (a -> a) -> a -> a
while pred body x = if pred x then while pred body (body x) else x

{-@ cond :: (Int, Int) -> Bool @-}
cond :: (Int, Int) -> Bool
cond (i, c) = i < 1000

{-@ loop :: (Int, Int) -> (Int, Int) @-}
loop :: (Int, Int) -> (Int, Int)
loop (i, c) = (i + 1, c + i)