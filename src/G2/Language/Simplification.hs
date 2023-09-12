-- Semantics-preserving syntactic transformations

{-# LANGUAGE FlexibleContexts #-}

module G2.Language.Simplification ( simplifyExprs
                                  , simplifyAppLambdas
                                  , inlineFunc
                                  , inlineFuncInCase) where

import G2.Language.AST
import G2.Language.Expr
import qualified G2.Language.ExprEnv as E
import G2.Language.Syntax
import G2.Language.Typing

import Data.List

simplifyExprs :: ASTContainer t Expr => E.ExprEnv -> E.ExprEnv -> t -> t
simplifyExprs eenv c_eenv = modifyContainedASTs (simplifyExpr eenv c_eenv)

simplifyExpr :: E.ExprEnv -> E.ExprEnv -> Expr -> Expr
simplifyExpr eenv c_eenv e =
    let
        e' = simplifyAppLambdas $ e
        -- e' = caseOfKnownCons
        --    . inlineFuncInCase c_eenv
        --    . inlineFunc eenv
        --    . simplifyAppLambdas $ e
    in
    if e == e' then e else simplifyExpr eenv c_eenv e'

-- | Reduce Lambdas that are being passed variables or values in SWHNF.
-- This AVOIDS reducing a lamba if it could cause us to miss an opportunity for sharing.
simplifyAppLambdas :: Expr -> Expr
simplifyAppLambdas (App (Lam TermL i e) e')
    | safeToInline e' = simplifyAppLambdas $ replaceVar (idName i) e' e
simplifyAppLambdas (App (Lam TypeL i e) (Var i')) =
    simplifyAppLambdas $ retype i (TyVar i') e
simplifyAppLambdas (App (Lam TypeL i e) (Type t)) =
    simplifyAppLambdas $ retype i t e
simplifyAppLambdas e@(App (App _ _) _) =
    let
        e' = modifyChildren simplifyAppLambdas e
    in
    if e == e' then e else simplifyAppLambdas e'
simplifyAppLambdas e = modifyChildren simplifyAppLambdas e

safeToInline :: Expr -> Bool
safeToInline (Var _) = True
safeToInline (Lit _) = True
safeToInline e@(App _ _) | Data _:_ <- unApp e = True
safeToInline e@(App _ _) | Prim _ _:_ <- unApp e = True
safeToInline _ = False

-- | Inline the functions in the ExprEnv
inlineFunc :: E.ExprEnv -> Expr -> Expr
inlineFunc eenv v@(Var (Id n _))
    | Just e <- E.lookup n eenv = inlineFunc eenv e
    | otherwise = v
inlineFunc eenv e =
    modifyChildren (inlineFunc eenv) e

-- | Inline the functions in the ExprEnv, if they are the bindee in a Case expression
inlineFuncInCase :: E.ExprEnv -> Expr -> Expr
inlineFuncInCase eenv c@(Case (Var (Id n _)) i t as)
    | Just e <- E.lookup n eenv =
        inlineFuncInCase eenv $ Case e i t as
    | otherwise = c
inlineFuncInCase eenv e =
    modifyChildren (inlineFuncInCase eenv) e

caseOfKnownCons :: Expr -> Expr
caseOfKnownCons (Case e i _ as)
--DCInstance caseOfKnownCons
    | Data (DataCon n t tyvars):es <- unApp e
    , Just (Alt (DataAlt _ is) ae) <- find (matchingDataAlt n) as =
        let
            tfa_count = length (leadingTyForAllBindings $ PresType t)
            es' = drop tfa_count es
        in
        foldr (uncurry replaceVar) (replaceVar (idName i) e ae) (zip (map idName is) es')
    | Lit l:_ <- unApp e
    , Just (Alt (LitAlt _) ae) <- find (matchingLitAlt l) as = replaceVar (idName i) e ae
    
    | Data _:_ <- unApp e
    , Just (Alt Default ae) <- find (\(Alt am _) -> am == Default) as = replaceVar (idName i) e ae
    | Lit l:_ <- unApp e
    , Just (Alt Default ae) <- find (\(Alt am _) -> am == Default) as = replaceVar (idName i) e ae

caseOfKnownCons e = modifyChildren caseOfKnownCons e

matchingDataAlt :: Name -> Alt -> Bool
matchingDataAlt n (Alt (DataAlt (DataCon n' _ _) _) _) = n == n'
matchingDataAlt _ _ = False

matchingLitAlt :: Lit -> Alt -> Bool
matchingLitAlt l (Alt (LitAlt l') _) = l == l'
matchingLitAlt _ _ = False