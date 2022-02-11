{-@ LIQUID "--no-termination" @-}

module M19 (main) where

{-@ main :: Int -> { b:Bool | b } @-}
main :: Int -> Bool
main flag =
    case while flag (0, 0) of
        (_, j) -> if flag >= 0 then j == 100 else True

{-@ while :: flag:Int
          -> xs:{ xs:(Int, Int) | (flag >= 0 => x_Tuple21 xs == x_Tuple22 xs) && x_Tuple21 xs <= 100 }
          -> { ys:(Int, Int) | (flag >= 0 => x_Tuple21 ys == x_Tuple22 ys) && x_Tuple21 ys == 100}@-}
while :: Int -> (Int, Int) -> (Int, Int)
while flag (b, j) = if b < 100
                        then while flag (if flag >= 0
                                            then (b + 1, j + 1)
                                            else (b + 1, j)
                                        )
                        else (b, j)