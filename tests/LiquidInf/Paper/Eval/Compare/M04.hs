{-@ LIQUID "--no-termination" @-}

module M04 (main) where

{-@ main :: Int -> { b:Bool | b } @-}
main :: Int -> Bool
main y = case while (-50, y) of
                (x', y') -> y' > 0

{-@ while :: (Int, Int) -> {t:(Int, Int) | not (fst t < 0) } @-}
while :: (Int, Int) -> (Int, Int)
while (x, y) = if x < 0 then while (x + y, y + 1) else (x, y)