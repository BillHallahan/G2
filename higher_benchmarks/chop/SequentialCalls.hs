{-# LANGUAGE BangPatterns #-}

module SequentialCalls where

import G2.Plugin

omega :: Int
omega = omega

{-# ANN sequentialCalls (SymExWithConfig "--max-outputs 1 --no-step-limit --time 300 --higher-order symbolic --search subpath --subpath-len 8 --accept-times --print-timeout-list-depth --smt cvc5")
    #-}
{-# ANN sequentialCalls (SymExWithConfig "--max-outputs 1 --no-step-limit --time 300 --higher-order sym-constraints --search subpath --subpath-len 8 --accept-times --print-timeout-list-depth --smt cvc5")
    #-}
sequentialCalls :: ((Int -> Int) -> Int) -> Int
sequentialCalls f =
    let
        !x = f (\n -> if n == 7 then 73 else omega)
    in
    let
        !y = f (\n -> if n == 7 then 64 else if n == 31 then error "REAL" else 73)
    in
    0