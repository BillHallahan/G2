module PeanoTest where

import G2.Internals.Language

import TestUtils

zeroPeano :: Expr
zeroPeano =
    Data $ DataCon (Name "Zero" (Module "Peano") 0) (TyConApp (Name "Peano" (Module "Peano") 0) []) []

succPeano :: Expr -> Expr
succPeano x =
    App (Data $ DataCon (Name "Succ" (Module "Peano") 0) (TyConApp (Name "Peano" (Module "Peano") 0) []) []) x

peano_0_4 :: [Expr] -> Bool
peano_0_4 [a, b] = a `eqIgT` zeroPeano && b `eqIgT` (succPeano . succPeano . succPeano . succPeano $ zeroPeano)
peano_0_4 _ = False

peano_1_3 :: [Expr] -> Bool
peano_1_3 [a, b] = a `eqIgT` (succPeano $ zeroPeano) && b `eqIgT` (succPeano . succPeano . succPeano $ zeroPeano)
peano_1_3 _ = False

peano_1_4 :: [Expr] -> Bool
peano_1_4 [a, b] = a `eqIgT` (succPeano $ zeroPeano) && b `eqIgT` (succPeano . succPeano . succPeano . succPeano $ zeroPeano)
peano_1_4 _ = False

peano_2_2 :: [Expr] -> Bool
peano_2_2 [a, b] = a `eqIgT` (succPeano . succPeano $ zeroPeano) && b `eqIgT` (succPeano . succPeano $ zeroPeano)
peano_2_2 _ = False

peano_3_1 :: [Expr] -> Bool
peano_3_1 = peano_1_3 . reverse

peano_4_0 :: [Expr] -> Bool
peano_4_0 = peano_0_4 . reverse

peano_4_1 :: [Expr] -> Bool
peano_4_1 = peano_1_4 . reverse