{-# LANGUAGE FlexibleContexts #-}

module G2.Initialization.ElimTicks (elimBreakpoints) where

import G2.Language

elimBreakpoints :: ASTContainer m Expr => m -> m
elimBreakpoints = modifyASTs elimBreakpoints'

elimBreakpoints' :: Expr -> Expr
elimBreakpoints' (Tick (Breakpoint _) e) = elimBreakpoints' e
elimBreakpoints' e = e