module TypeClassTest where

import G2.Internals.Language

import TestUtils

tc3Holds :: Expr -> Expr -> Bool
tc3Holds (Lit (LitInt a)) (Lit (LitInt b)) = a + 8 == b
tc3Holds _ _ = False


