{-@ LIQUID "--no-termination" @-}

module M27 (main) where

{-@ main :: Int -> l:{ l:Int | l > 0 } -> (Int, Int, Int) @-}
main :: Int -> Int -> (Int, Int, Int)
main n l = while cond1 loop1 (1, n, l)

while :: (a -> Bool) -> (a -> a) -> a -> a
while pred body x = if pred x then while pred body (body x) else x

{-@ cond1 :: (Int, Int, Int) -> Bool @-}
cond1 :: (Int, Int, Int) -> Bool
cond1 (k, n, l) = k < n

{-@ loop1 :: (Int, Int, Int) -> (Int, Int, Int) @-}
loop1 :: (Int, Int, Int) -> (Int, Int, Int)
loop1 (k, n, l) =
    case while cond2 loop2 (k, l, n) of
        (k', i', n') -> (k' + 1, n', l)

{-@ cond2 :: (Int, Int, Int) -> Bool @-}
cond2 :: (Int, Int, Int) -> Bool
cond2 (k, i, n) = i < n

{-@ loop2 :: (Int, Int, Int) -> (Int, Int, Int) @-}
loop2 :: (Int, Int, Int) -> (Int, Int, Int)
loop2 (k, i, n) =
    case 1 <= k of
        True -> (k, i + 1, n)
        False -> error "bad"