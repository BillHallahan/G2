{-@ LIQUID "--no-termination" @-}

module M24 (main) where

{-@ main :: Int -> { b:Bool | b } @-}
main :: Int -> Bool
main n =
    case while cond1 loop1 (0, n) of
        _ -> True

while :: (a -> Bool) -> (a -> a) -> a -> a
while pred body x = if pred x then while pred body (body x) else x

{-@ cond1 :: (Int, Int) -> Bool @-}
cond1 :: (Int, Int) -> Bool
cond1 (i, n) = i < n

{-@ loop1 :: (Int, Int) -> (Int, Int) @-}
loop1 :: (Int, Int) -> (Int, Int)
loop1 (i, n) =
    case while cond2 loop2 (i, i, n) of
        (i', _, n') -> (i' + 1, n')

{-@ cond2 :: (Int, Int, Int) -> Bool @-}
cond2 :: (Int, Int, Int) -> Bool
cond2 (i, j, n) = j < n

{-@ loop2 :: (Int, Int, Int) -> (Int, Int, Int) @-}
loop2 :: (Int, Int, Int) -> (Int, Int, Int)
loop2 (i, j, n) =
    case while cond3 loop3 (i, j, j, n) of
        (i', j', _, n') -> (i', j' + 1, n')

{-@ cond3 :: (Int, Int, Int, Int) -> Bool @-}
cond3 :: (Int,Int, Int, Int) -> Bool
cond3 (i, j, k, n) = k < n

{-@ loop3 :: (Int, Int, Int, Int) -> (Int, Int, Int, Int) @-}
loop3 :: (Int, Int, Int, Int) -> (Int, Int, Int, Int)
loop3 (i, j, k, n) =
    case k >= i of
        True -> (i, j, k + 1, n)
        False -> error "bad"