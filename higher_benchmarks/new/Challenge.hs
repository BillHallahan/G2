module Challenge where

import Control.Exception
import G2.Plugin

data AB = A AB | B deriving Eq

{-# NOINLINE abInf #-}
abInf :: () -> AB
abInf = abInf

{-# NOINLINE b #-}
b :: () -> AB
b () = A B

data XYZ = X | Y | Z

{-# ANN abc1 (SymExWithConfig "--max-outputs 1 --no-step-limit --time 300 --higher-order symbolic --error-asserts --search subpath --subpath-len 8 --accept-times --print-timeout-list-depth --smt cvc5")
    #-}
{-# ANN abc1 (SymExWithConfig "--max-outputs 1 --no-step-limit --time 300 --higher-order sym-constraints --search subpath --subpath-len 8 --accept-times --print-timeout-list-depth --smt cvc5")
    #-}
abc1 :: (Int -> AB -> XYZ) -> Int
abc1 f = case f 1 B of
                X -> case f 1 (A B) of
                            Y -> case f 2 (abInf ()) of
                                    Z -> error "REAL"
                                    _ -> 2
                            _ -> 3
                _ -> 4

{-# ANN abc2 (SymExWithConfig "--max-outputs 1 --no-step-limit --time 300 --higher-order symbolic --search subpath --subpath-len 8 --accept-times --print-timeout-list-depth --smt cvc5")
    #-}
{-# ANN abc2 (SymExWithConfig "--max-outputs 1 --no-step-limit --time 300 --higher-order sym-constraints --search subpath --subpath-len 8 --accept-times --print-timeout-list-depth --smt cvc5")
    #-}
abc2 :: (Int -> AB -> AB -> XYZ) -> Int
abc2 f =
    case f 1 (A B) B of
        X -> case f 1 (A (b ())) (abInf ()) of
                Y -> error "REAL"
                _ -> 2
        _ -> 3

{-# ANN abc3 (SymExWithConfig "--max-outputs 1 --no-step-limit --time 300 --higher-order symbolic --search subpath --subpath-len 8 --accept-times --print-timeout-list-depth --smt cvc5")
    #-}
{-# ANN abc3 (SymExWithConfig "--max-outputs 1 --no-step-limit --time 300 --higher-order sym-constraints --search subpath --subpath-len 8 --accept-times --print-timeout-list-depth --smt cvc5")
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

{-# ANN abc4 (SymExWithConfig "--max-outputs 1 --no-step-limit --time 300 --higher-order symbolic --search subpath --subpath-len 8 --accept-times --print-timeout-list-depth --smt cvc5")
    #-}
{-# ANN abc4 (SymExWithConfig "--max-outputs 1 --no-step-limit --time 300 --higher-order sym-constraints --search subpath --subpath-len 8 --accept-times --print-timeout-list-depth --smt cvc5")
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

{-# ANN funcs (SymExWithConfig "--max-outputs 1 --no-step-limit --time 300 --higher-order symbolic --search subpath --subpath-len 8 --accept-times --print-timeout-list-depth --smt cvc5")
    #-}
{-# ANN funcs (SymExWithConfig "--max-outputs 1 --no-step-limit --time 300 --higher-order sym-constraints --search subpath --subpath-len 8 --accept-times --print-timeout-list-depth --smt cvc5")
    #-}
funcs :: (Funcs -> Int) -> Int
funcs f =
    case f (I (\x -> x)) == f (I (\x -> x + 1)) of
        True -> 1
        False -> case f (B2 (> 0)) == f (B2 (< 10)) of
                    True -> error "REAL"
                    False -> 3

{-# ANN maybeFuncs (SymExWithConfig "--max-outputs 1 --no-step-limit --time 300 --higher-order symbolic --search subpath --subpath-len 8 --accept-times --print-timeout-list-depth --smt cvc5")
    #-}
{-# ANN maybeFuncs (SymExWithConfig "--max-outputs 1 --no-step-limit --time 300 --higher-order sym-constraints --search subpath --subpath-len 8 --accept-times --print-timeout-list-depth --smt cvc5")
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
