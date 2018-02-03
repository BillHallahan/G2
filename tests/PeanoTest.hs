{-# LANGUAGE OverloadedStrings #-}

module PeanoTest where

import G2.Internals.Language

import TestUtils

zeroPeano :: Expr
zeroPeano =
    Data $ DataCon (Name "Zero" (Just "Peano") 0) (TyConApp (Name "Peano" (Just "Peano") 0) []) []

succPeano :: Expr -> Expr
succPeano x =
    App (Data $ DataCon (Name "Succ" (Just "Peano") 0) (TyConApp (Name "Peano" (Just "Peano") 0) []) []) x

peano_0_4 :: [Expr] -> Bool
peano_0_4 [a, b, c] = a `eqIgT` zeroPeano && b `eqIgT` (succPeano . succPeano . succPeano . succPeano $ zeroPeano)
                      && c `eqIgT` (succPeano . succPeano . succPeano . succPeano $ zeroPeano)
peano_0_4 _ = False

peano_1_3 :: [Expr] -> Bool
peano_1_3 [a, b, c] = a `eqIgT` (succPeano $ zeroPeano) && b `eqIgT` (succPeano . succPeano . succPeano $ zeroPeano)
                   && c `eqIgT` (succPeano . succPeano . succPeano . succPeano $ zeroPeano)
peano_1_3 _ = False

peano_1_4 :: [Expr] -> Bool
peano_1_4 [a, b, c] = a `eqIgT` (succPeano $ zeroPeano) && b `eqIgT` (succPeano . succPeano . succPeano . succPeano $ zeroPeano)
                      && c `eqIgT` (succPeano . succPeano . succPeano . succPeano $ zeroPeano)
peano_1_4 _ = False

peano_2_2 :: [Expr] -> Bool
peano_2_2 [a, b, c] = a `eqIgT` (succPeano . succPeano $ zeroPeano) && b `eqIgT` (succPeano . succPeano $ zeroPeano)
                   && c `eqIgT` (succPeano . succPeano . succPeano . succPeano $ zeroPeano)
peano_2_2 _ = False

peano_3_1 :: [Expr] -> Bool
peano_3_1 [a, b, c] = peano_1_3 [b, a, c]
peano_3_1 _ = False

peano_4_0 :: [Expr] -> Bool
peano_4_0 [a, b, c] = peano_0_4 [b, a, c]
peano_4_0 _ = False

peano_4_1 :: [Expr] -> Bool
peano_4_1 [a, b, c] = peano_1_4 [b, a, c]
peano_4_1 _ = False

peano_4_out :: [Expr] -> Bool
peano_4_out [_, _, a] = a `eqIgT` (succPeano . succPeano . succPeano . succPeano $ zeroPeano)
peano_4_out _ = False

peano_1_4_5 :: [Expr] -> Bool
peano_1_4_5 [a, b, c] = a `eqIgT` (succPeano $ zeroPeano) && b `eqIgT` (succPeano . succPeano . succPeano . succPeano $ zeroPeano)
                      && c `eqIgT` (succPeano . succPeano . succPeano . succPeano . succPeano $ zeroPeano)
peano_1_4_5 _ = False

peano_4_1_5 :: [Expr] -> Bool
peano_4_1_5 [a, b, c] = peano_1_4_5 [b, a, c]
peano_4_1_5 _ = False
