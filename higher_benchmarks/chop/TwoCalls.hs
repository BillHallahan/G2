module TwoCalls where

equals :: Int -> Int -> Int
equals n m = if n == m then 0 else 1

twoCalls :: ((Int -> Int) -> Int) -> Int
twoCalls f =
    if f (equals 2) == 12 && f (equals 30) == 5 && f (equals 7) == -2
        then error "REAL"
        else 0