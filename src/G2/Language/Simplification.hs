-- Semantics-preserving syntactic transformations

{-# LANGUAGE FlexibleContexts #-}

module G2.Language.Simplification ( simplifyExprs
                                  , simplifyAppLambdas
                                  , inlineFunc
                                  , inlineFuncInCase) where

import G2.Execution.NormalForms
import G2.Language.AST
import G2.Language.Expr
import qualified G2.Language.ExprEnv as E
import G2.Language.Syntax
import G2.Language.Typing

simplifyExprs :: ASTContainer t Expr => E.ExprEnv -> E.ExprEnv -> t -> t
simplifyExprs eenv c_eenv = modifyContainedASTs (simplifyExpr eenv c_eenv)

simplifyExpr :: E.ExprEnv -> E.ExprEnv -> Expr -> Expr
simplifyExpr eenv c_eenv e =
    let
        e' = inlineFunc eenv
           . simplifyDefCase eenv
           . simplifyAppLambdas
           . stripAllTicks $ e
        -- e' = caseOfKnownCons
        --    . inlineFuncInCase c_eenv
        --    . inlineFunc eenv
        --    . simplifyAppLambdas $ e
    in
    if e == e' then e else simplifyExpr eenv c_eenv e'

-- | Reduce Lambdas that are being passed variables or values in SWHNF.
-- This AVOIDS reducing a lamba if it could cause us to miss an opportunity for sharing.
simplifyAppLambdas :: Expr -> Expr
simplifyAppLambdas (App (Lam TermL i e) e') =
    simplifyAppLambdas $ replaceVar (idName i) e' e
simplifyAppLambdas (App (Lam TypeL i e) (Var i')) =
    simplifyAppLambdas $ retype i (TyVar i') e
simplifyAppLambdas (App (Lam TypeL i e) (Type t)) =
    simplifyAppLambdas $ retype i t e
simplifyAppLambdas e = modifyChildren simplifyAppLambdas e

simplifyDefCase :: E.ExprEnv -> Expr -> Expr
simplifyDefCase eenv (Case e i _ [Alt Default e']) | isExprValueForm eenv e =
    simplifyDefCase eenv $ replaceVar (idName i) e e'
simplifyDefCase eenv e = modifyChildren (simplifyDefCase eenv) e

-- | Inline the functions in the ExprEnv
inlineFunc :: E.ExprEnv -> Expr -> Expr
inlineFunc eenv v@(Var (Id n _))
    | Just (E.Conc e) <- E.lookupConcOrSym n eenv = inlineFunc eenv e
    | otherwise = v
inlineFunc eenv e =
    modifyChildren (inlineFunc eenv) e

-- | Inline the functions in the ExprEnv, if they are the bindee in a Case expression
inlineFuncInCase :: E.ExprEnv -> Expr -> Expr
inlineFuncInCase eenv c@(Case (Var (Id n _)) i t as)
    | Just (E.Conc e) <- E.lookupConcOrSym n eenv =
        inlineFuncInCase eenv $ Case e i t as
    | otherwise = c
inlineFuncInCase eenv e =
    modifyChildren (inlineFuncInCase eenv) e
