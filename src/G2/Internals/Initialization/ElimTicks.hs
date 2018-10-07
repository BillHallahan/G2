{-# LANGUAGE FlexibleContexts #-}

module G2.Internals.Initialization.ElimTicks (elimTicks) where

import G2.Internals.Language

elimTicks :: ASTContainer m Expr => m -> m
elimTicks = modifyASTsFix elimTicks'

elimTicks' :: Expr -> Expr
elimTicks' (Tick _ e) = e
elimTicks' e = e
