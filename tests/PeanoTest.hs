module PeanoTest where

import G2.Internals.Core.Language

import Data.List

zeroPeano = Var "Zero" (TyConApp "Peano" [])

succPeano x = App (Var "Succ" (TyConApp "Peano" [])) x

peano_0_4 :: [Expr] -> Bool
peano_0_4 [a, b] = a == zeroPeano && b == (succPeano . succPeano . succPeano . succPeano $ zeroPeano)
peano_0_4 _ = False

peano_1_3 :: [Expr] -> Bool
peano_1_3 [a, b] = a == (succPeano $ zeroPeano) && b == (succPeano . succPeano . succPeano $ zeroPeano)
peano_1_3 _ = False

peano_1_4 :: [Expr] -> Bool
peano_1_4 [a, b] = a == (succPeano $ zeroPeano) && b == (succPeano . succPeano . succPeano . succPeano $ zeroPeano)
peano_1_4 _ = False

peano_2_2 :: [Expr] -> Bool
peano_2_2 [a, b] = a == (succPeano . succPeano $ zeroPeano) && b == (succPeano . succPeano $ zeroPeano)
peano_2_2 _ = False

peano_3_1 :: [Expr] -> Bool
peano_3_1 = peano_1_3 . reverse

peano_4_0 :: [Expr] -> Bool
peano_4_0 = peano_0_4 . reverse

peano_4_1 :: [Expr] -> Bool
peano_4_1 = peano_1_4 . reverse
