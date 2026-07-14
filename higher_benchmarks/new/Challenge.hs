module Challenge where

import G2.Plugin
import Control.Exception

data AB = A AB | B deriving Eq

{-# NOINLINE abInf #-}
abInf :: () -> AB
abInf = abInf

{-# NOINLINE b #-}
b :: () -> AB
b () = A B

data XYZ = X | Y | Z

{-# ANN abc1 (SymExWithConfig "--max-outputs 1 --no-step-limit --time 300 --higher-order symbolic --search subpath --subpath-len 8 --accept-times --print-timeout-list-depth --smt cvc5 --check-asserts --error-asserts")
    #-}
{-# ANN abc1 (SymExWithConfig "--max-outputs 1 --no-step-limit --time 300 --higher-order sym-constraints --search subpath --subpath-len 8 --accept-times --print-timeout-list-depth --smt cvc5 --check-asserts --error-asserts")
    #-}
abc1 :: (Int -> AB -> XYZ) -> Int
abc1 f = case f 1 B of
                X -> case f 1 (A B) of
                            Y -> case f 2 (abInf ()) of
                                    Z -> error "REAL"
                                    _ -> 2
                            _ -> 3
                _ -> 4

{-# ANN abc2 (SymExWithConfig "--max-outputs 1 --no-step-limit --time 300 --higher-order symbolic --search subpath --subpath-len 8 --accept-times --print-timeout-list-depth --smt cvc5 --check-asserts --error-asserts")
    #-}
{-# ANN abc2 (SymExWithConfig "--max-outputs 1 --no-step-limit --time 300 --higher-order sym-constraints --search subpath --subpath-len 8 --accept-times --print-timeout-list-depth --smt cvc5 --check-asserts --error-asserts")
    #-}
abc2 :: (Int -> AB -> AB -> XYZ) -> Int
abc2 f =
    case f 1 (A B) B of
        X -> case f 1 (A (b ())) (abInf ()) of
                Y -> error "REAL"
                _ -> 2
        _ -> 3

{-# ANN abc3 (SymExWithConfig "--max-outputs 1 --no-step-limit --time 300 --higher-order symbolic --search subpath --subpath-len 8 --accept-times --print-timeout-list-depth --smt cvc5 --check-asserts --error-asserts")
    #-}
{-# ANN abc3 (SymExWithConfig "--max-outputs 1 --no-step-limit --time 300 --higher-order sym-constraints --search subpath --subpath-len 8 --accept-times --print-timeout-list-depth --smt cvc5 --check-asserts --error-asserts")
    #-}
abc3 :: (Int -> AB -> Bool) -> Int
abc3 f =
    case f 1 (abInf ()) of
        True -> case f 2 (A B) of
                    True -> case f 2 B of
                                False -> error "REAL"
                                _ -> 2
                    _ -> 3
        _ -> 4

{-# ANN abc4 (SymExWithConfig "--max-outputs 1 --no-step-limit --time 300 --higher-order symbolic --search subpath --subpath-len 8 --accept-times --print-timeout-list-depth --smt cvc5 --check-asserts --error-asserts")
    #-}
{-# ANN abc4 (SymExWithConfig "--max-outputs 1 --no-step-limit --time 300 --higher-order sym-constraints --search subpath --subpath-len 8 --accept-times --print-timeout-list-depth --smt cvc5 --check-asserts --error-asserts")
    #-}
abc4 :: (AB -> Int -> Bool) -> Int
abc4 f =
    case f (abInf ()) 1 of
        True -> case f (A B) 2 of
                    True -> case f B 2 of
                                False -> error "REAL"
                                _ -> 2
                    _ -> 3
        _ -> 4

data Funcs = I (Int -> Int) | I2 (Int -> Int -> Int) | B2 (Int -> Bool)

{-# ANN funcs (SymExWithConfig "--max-outputs 1 --no-step-limit --time 300 --higher-order symbolic --search subpath --subpath-len 8 --accept-times --print-timeout-list-depth --smt cvc5 --check-asserts --error-asserts")
    #-}
{-# ANN funcs (SymExWithConfig "--max-outputs 1 --no-step-limit --time 300 --higher-order sym-constraints --search subpath --subpath-len 8 --accept-times --print-timeout-list-depth --smt cvc5 --check-asserts --error-asserts")
    #-}
funcs :: (Funcs -> Int) -> Int
funcs f =
    case f (I (\x -> x)) == f (I (\x -> x + 1)) of
        True -> 1
        False -> case f (B2 (> 0)) == f (B2 (< 10)) of
                    True -> error "REAL"
                    False -> 3

{-# ANN maybeFuncs (SymExWithConfig "--max-outputs 1 --no-step-limit --time 300 --higher-order symbolic --search subpath --subpath-len 8 --accept-times --print-timeout-list-depth --smt cvc5 --check-asserts --error-asserts")
    #-}
{-# ANN maybeFuncs (SymExWithConfig "--max-outputs 1 --no-step-limit --time 300 --higher-order sym-constraints --search subpath --subpath-len 8 --accept-times --print-timeout-list-depth --smt cvc5 --check-asserts --error-asserts")
    #-}
maybeFuncs :: (Maybe Funcs -> Int) -> Int
maybeFuncs f =
    case f (Just (I id)) == f Nothing of
        True -> 1
        False -> case f (Just (I id)) == f (Just (B2 $ const True)) of
                    True -> case f (Just (I id)) == f (Just (I (\x -> x * 2))) of
                                True -> error "REAL"
                                False -> 3
                    False -> 4

{-# ANN retFunc (SymExWithConfig "--max-outputs 1 --no-step-limit --time 300 --higher-order symbolic --search subpath --subpath-len 8 --accept-times --print-timeout-list-depth --smt cvc5 --check-asserts --error-asserts")
    #-}
{-# ANN retFunc (SymExWithConfig "--max-outputs 1 --no-step-limit --time 300 --higher-order sym-constraints --search subpath --subpath-len 8 --accept-times --print-timeout-list-depth --smt cvc5 --check-asserts --error-asserts")
    #-}
retFunc :: (Int -> [Int -> Int]) -> Int
retFunc g =
    case g 1 of
        [h] -> case g (one ()) of
                    [k] -> case h 2 == k 2 of
                                    True -> 1
                                    False -> 2 -- Unreachable
        [_, h] -> case g (one ()) of
                    [_, k] -> case h 2 == k 2 of
                                    True -> error "REAL"
                                    False -> 4 -- Unreachable
        (_:_:_:_) -> 5
        _ -> 6

{-# NOINLINE one #-}
one :: () -> Int
one _ = 1
