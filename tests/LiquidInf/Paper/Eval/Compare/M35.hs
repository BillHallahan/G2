{-@ LIQUID "--no-termination" @-}

module M35 (main) where

{-@ main :: Int -> { b:Bool | b } @-}
main :: Int -> Bool
main n = case while (n, 0) of
                (n', x) -> if n' > 0 then x == n' else True

-- {-@ while :: i:{ t:(Int, Int) | fst t <= 0 || snd t <= fst t } -> { t:(Int, Int) | fst t <= 0 || snd t == fst t } @-}
while :: (Int, Int) -> (Int, Int)
while (n, x) = if x < n then while (n, x + 1) else (n, x)