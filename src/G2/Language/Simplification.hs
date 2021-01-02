-- Semantics-preserving syntactic transformations

{-# LANGUAGE FlexibleContexts #-}

module G2.Language.Simplification ( simplifyExprs
                                  , simplifyAppLambdas) where

import G2.Language.AST
import G2.Language.Expr
import G2.Language.Syntax
import G2.Language.Typing

import Data.Function

simplifyExprs :: ASTContainer t Expr => t -> t
simplifyExprs = modifyContainedASTs simplifyExpr

simplifyExpr :: Expr -> Expr
simplifyExpr = simplifyAppLambdas

simplifyAppLambdas :: Expr -> Expr
simplifyAppLambdas (App (Lam TermL i e) e')
    | safeToInline e' = simplifyAppLambdas $ replaceVar (idName i) e' e
simplifyAppLambdas (App (Lam TypeL i e) (Var i')) =
    simplifyAppLambdas $ retype i (TyVar i') e
simplifyAppLambdas e@(App (App _ _) _) =
    let
        e' = modifyChildren simplifyAppLambdas e
    in
    if e == e' then e else simplifyAppLambdas e'
simplifyAppLambdas e = modifyChildren simplifyAppLambdas e

safeToInline :: Expr -> Bool
safeToInline (Var _) = True
safeToInline (Lit _) = True
safeToInline _ = False