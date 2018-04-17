{-# LANGUAGE FlexibleContexts #-}

module G2.Internals.Initialization.InitVarLocs (initVarLocs) where

import G2.Internals.Language

initVarLocs :: ASTContainer m Expr => m -> m
initVarLocs = modifyASTs initVarLocs'

initVarLocs' :: Expr -> Expr
initVarLocs' (Tick (Breakpoint l) e)
    | (Var (Id (Name n m i _) t)):xs <- unApp e =
    mkApp (Var (Id (Name n m i (Just l)) t):xs)
initVarLocs' e = e