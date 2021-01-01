-- Semantics-preserving syntactic transformations

{-# LANGUAGE FlexibleContexts #-}

module G2.Language.Simplification ( simplifyExpr
                                  , simplifyAppLambdas) where

import G2.Language.AST
import G2.Language.Expr
import G2.Language.Syntax

import Data.Function

simplifyExpr :: ASTContainer t Expr => t -> t
simplifyExpr = modifyContainedASTs simplifyExpr'

simplifyExpr' :: Expr -> Expr
simplifyExpr' = simplifyAppLambdas

simplifyAppLambdas :: Expr -> Expr
simplifyAppLambdas (App (Lam _ i e) e')
    | safeToInline e' = simplifyAppLambdas $ replaceVar (idName i) e' e
simplifyAppLambdas e@(App (App _ _) _) =
    let
        e' = modifyChildren simplifyAppLambdas e
    in
    if e == e' then e else simplifyAppLambdas e'
simplifyAppLambdas e = e

safeToInline :: Expr -> Bool
safeToInline (Var _) = True
safeToInline (Lit _) = True
safeToInline _ = False