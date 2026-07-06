-- Converted from:
-- https://github.com/shhyou/chop-esop-supplementary/blob/main/benchmarks/concolic-hop/calls-functions/reverse-args.rkt

module ReverseArgs where

omega :: Int
omega = omega

reverseArgs :: ((Int -> Int) -> Int -> Int) -> Int
reverseArgs f =
    let
        n1 = f (\n -> if n == 0 then 10 else omega) 0
        n2 = f (\n -> if n == 0 then 23 else omega) 0
        n3 = f (\m -> if m == 1 then 37 else omega) 1
        n4 = f (\m -> if m == 1 then 41 else omega) 1
    in
    if n1 == 12 && n2 == 34 && n3 == 56 && n4 == 78
        then error "REAL"
        else 0