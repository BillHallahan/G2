{-# LANGUAGE FlexibleContexts #-}

module G2.Internals.Initialization.InitVarLocs (initVarLocs) where

import G2.Internals.Language

initVarLocs :: ASTContainer m Expr => m -> m
initVarLocs = modifyASTs initVarLocs'

initVarLocs' :: Expr -> Expr
initVarLocs' (Tick (Breakpoint brs) e)
    | (Var (Id (Name n m i (Just vs)) t)):xs <- unApp e =
    let
        s' = adjustSpanLoc brs vs
    in
    mkApp (Var (Id (Name n m i (Just s')) t):xs)
initVarLocs' e = e

-- | Returns a span with the first spans
-- start location, but with the same length as the second span
adjustSpanLoc :: Span -> Span -> Span
adjustSpanLoc sp1@(Span {end = en}) sp2 =
    let
        re_line = (line $ end sp2) - (line $ start sp2)
        re_col = (col $ end sp2) - (col $ start sp2)
    
        e_line = (line $ start sp1) + re_line
        e_col = (col $ start sp2) + re_col
    in
    sp1 {end = en { line = e_line
                  , col = e_col}
        }