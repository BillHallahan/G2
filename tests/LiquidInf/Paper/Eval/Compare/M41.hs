{-@ LIQUID "--no-termination" @-}

module M41 (main) where

{-@ main :: n:{ n:Int | n >= 0 } -> poss_k:{ n:Int | poss_k >= 0 } -> Int -> { b:Bool | b } @-}
main :: Int -> Int -> Int -> Bool
main n poss_k flag =
    let
        k = if flag >= 0 then poss_k else 1
    in
    case while n k (0, 0) of
        (i', j') -> k + i' + j' > 2 * n

{-@ while :: n:Int -> Int -> (Int, Int) ->{t:(Int, Int) | not (fst t <= n) } @-}
while :: Int -> Int -> (Int, Int) -> (Int, Int)
while n k (i, j) = if i <= n then while n k (i + 1, j + i + 1) else (i, j)
