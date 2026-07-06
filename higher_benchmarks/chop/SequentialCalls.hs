module SequentialCalls where

omega :: Int
omega = omega

sequentialCalls :: ((Int -> Int) -> Int) -> Int
sequentialCalls f =
    let
        !x = f (\n -> if n == 7 then 73 else omega)
    in
    let
        !y = f (\n -> if n == 7 then 64 else if n == 31 then error "REAL" else 73)
    in
    0