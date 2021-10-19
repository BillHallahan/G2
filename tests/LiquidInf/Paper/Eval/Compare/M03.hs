{-@ LIQUID "--no-termination" @-}

module M15 (main) where

{-@ main :: Int -> { l:Int | l > 0} -> Bool @-}
main :: Int -> Int -> Bool
main n l = case while cond1 loop1 (1,n,l) of
                (k, n', l') -> True

while :: (a -> Bool) -> (a -> a) -> a -> a
while pred body x = if pred x then while pred body (body x) else x

{-@ cond1 :: (Int, Int, Int) -> Bool @-}
cond1 :: (Int, Int, Int) -> Bool
cond1 (k, n, l) = k < n

{-@ cond2 :: (Int, Int) -> Bool @-}
cond2 :: (Int, Int) -> Bool
cond2 (i, n) = i < n

{-@ loop1 :: (Int, Int, Int) -> (Int, Int, Int) @-}
loop1 :: (Int, Int, Int) -> (Int, Int, Int)
loop1 (k, n, l) =
    let
        (i', n') = while cond2 loop2 (l, n)
    in
    (k + 1, n', l)

{-@ loop2 :: (Int, Int) -> (Int, Int) @-}
loop2 :: (Int, Int) -> (Int, Int)
loop2 (i, n) =
    case 1 <= i of
        True -> (i + 1, n)
        False -> error "bad!"