{-@ LIQUID "--no-termination" @-}

module M19 (main) where

{-@ main :: Int -> { b:Bool | b } @-}
main :: Int -> Bool
main flag =
    case while (flag, 0, 0) of
        (_, _, j) -> if flag >= 0 then j == 100 else True

-- {-@ while :: xs:{ xs:(Int, Int, Int) | (x_Tuple31 xs < 0 || x_Tuple32 xs == x_Tuple33 xs) && x_Tuple32 xs <= 100 }
--           -> { ys:(Int, Int, Int) | (x_Tuple31 xs < 0 || x_Tuple32 ys == x_Tuple33 ys) && x_Tuple32 ys == 100}@-}
while :: (Int, Int, Int) -> (Int, Int, Int)
while (flag, b, j) = if b < 100
                        then while (if flag >= 0
                                        then (flag, b + 1, j + 1)
                                        else (flag, b + 1, j)
                                   )
                        else (flag, b, j)