{-@ LIQUID "--no-termination" @-}

module M19 (main) where

{-@ main :: { b:Bool | b } @-}
main :: Bool
main =
    case while (0, 0, 100) of
        (j', i', x') -> j' == 2 * x'

while :: (Int, Int, Int) -> (Int, Int, Int)
while (j, i, x) = if i < x then while (j + 2, i + 1, x) else (j, i, x)