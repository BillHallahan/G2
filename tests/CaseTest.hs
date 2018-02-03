{-# LANGUAGE OverloadedStrings #-}

module CaseTest where

import G2.Internals.Language
import TestUtils

exists1 :: [Expr] -> Bool
exists1 [(App x y), (App z w)] =
    dcHasName "A" x && dcHasName "B" y && dcHasName "A" z && dcHasName "C" w
exists1 _ = False

exists2 :: [Expr] -> Bool
exists2 [x, y] = dcHasName "B" x && dcHasName "C" y
exists2 _ = False

exists3 :: [Expr] -> Bool
exists3 [x, (App y (App z w))] =
    dcHasName "C" x && dcHasName "A" y && dcHasName "A" z && dcHasName "B" w
exists3 _ = False

exists4 :: [Expr] -> Bool
exists4 [_, (App y z)] = dcHasName "A" y && dcHasName "B" z
exists4 _ = False