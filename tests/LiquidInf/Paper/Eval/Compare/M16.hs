{-@ LIQUID "--no-termination" @-}

module M16 (main) where

{-@ main :: Int -> Int -> { b:Bool | b } @-}
main :: Int -> Int -> Bool
main i j = case while (i, j, i, j) of
                (i', j', x, y) -> if i' == j' then y == 0 else True

{-@ while :: (Int, Int, Int, Int) -> {t:(Int, Int, Int, Int) | not (x_Tuple43 t /= 0)} @-}
while :: (Int, Int, Int, Int) -> (Int, Int, Int, Int)
while (i, j, x, y) = if x /= 0 then while (i, j, x - 1, y - 1) else (i, j, x, y)