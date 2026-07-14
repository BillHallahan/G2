module TwoCalls where

import G2.Plugin

equals :: Int -> Int -> Int
equals n m = if n == m then 0 else 1

{-# ANN twoCalls (SymExWithConfig "--max-outputs 1 --no-step-limit --time 300 --higher-order symbolic --search subpath --subpath-len 8 --accept-times --print-timeout-list-depth --smt cvc5 --check-asserts --error-asserts")
    #-}
{-# ANN twoCalls (SymExWithConfig "--max-outputs 1 --no-step-limit --time 300 --higher-order sym-constraints --search subpath --subpath-len 8 --accept-times --print-timeout-list-depth --smt cvc5 --check-asserts --error-asserts")
    #-}
twoCalls :: ((Int -> Int) -> Int) -> Int
twoCalls f =
    if f (equals 2) == 12 && f (equals 30) == 5 && f (equals 7) == -2
        then error "REAL"
        else 0