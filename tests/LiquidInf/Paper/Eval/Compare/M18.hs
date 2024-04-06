{-@ LIQUID "--no-termination" @-}

module M19 (main) where

{-@ main :: Int -> { b:Bool | b } @-}
main :: Int -> Bool
main flag =
    case while flag (0, 0) of
        (_, j) -> if flag >= 0 then j == 100 else True

{-@ while :: Int -> (Int, Int) -> { t:(Int, Int) | not (fst t < 100 )} @-}
while :: Int -> (Int, Int) -> (Int, Int)
while flag (b, j) = if b < 100
                        then while flag (if flag >= 0
                                            then (b + 1, j + 1)
                                            else (b + 1, j)
                                        )
                        else (b, j)