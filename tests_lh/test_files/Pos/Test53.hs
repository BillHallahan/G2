{-@ LIQUID "--no-termination" @-}

module M15 (main) where

{-@ main :: { b:Bool | b } @-}
main :: Bool
main = while cond loop 0 >= 0

while :: (a -> Bool) -> (a -> a) -> a -> a
while pred body x = if pred x then while pred body (body x) else x

{-@ cond :: Int -> Bool @-}
cond :: Int -> Bool
cond j = j < 1

{-@ loop :: Int -> Int  @-}
loop :: Int -> Int
loop j = 100