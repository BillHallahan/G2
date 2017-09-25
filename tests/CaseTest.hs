module CaseTest where

import G2.Internals.Language
import TestUtils

exists1 :: [Expr] -> Bool
exists1 [(App x y), (App z w)] =
	dataConHasName "A" x && dataConHasName "B" y && dataConHasName "A" z && dataConHasName "C" w
exists1 _ = False

exists2 :: [Expr] -> Bool
exists2 [x, y] = dataConHasName "B" x && dataConHasName "C" y

exists3 :: [Expr] -> Bool
exists3 [x, (App y (App z w))] =
	dataConHasName "C" x && dataConHasName "A" y && dataConHasName "A" z && dataConHasName "B" w
exists3 _ = False

exists4 :: [Expr] -> Bool
exists4 [x, (App y z)] = dataConHasName "A" y && dataConHasName "B" z
exists4 _ = False