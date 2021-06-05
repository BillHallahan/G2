{-# LANGUAGE FlexibleContexts #-}

module G2.Initialization.ElimTicks (elimTicks) where

import G2.Language

elimTicks :: ASTContainer m Expr => m -> m
elimTicks = modifyASTs elimTicks'

elimTicks' :: Expr -> Expr
elimTicks' (Tick _ e) = elimTicks' e
elimTicks' e = e