{-# LANGUAGE FlexibleContexts #-}

module G2.Internals.Liquid.SimplifyAsserts (simplifyAsserts) where

import G2.Internals.Language
import G2.Internals.Language.KnownValues
import G2.Internals.Liquid.TCValues

import Debug.Trace

type ModifiedKnownValues = KnownValues

simplifyAsserts :: (ASTContainer h Expr, ASTContainer t Expr) => ModifiedKnownValues -> TCValues -> State h t -> State h t
simplifyAsserts mkv tcv s@(State {type_env = tenv, known_values = kv}) =
    modifyASTs (simplifyAsserts' tenv kv mkv tcv) s

simplifyAsserts' :: TypeEnv -> KnownValues -> ModifiedKnownValues -> TCValues -> Expr -> Expr
simplifyAsserts' tenv kv mkv tcv (Assume a e) = Assume (simplifyIn tenv kv mkv tcv a) e
simplifyAsserts' tenv kv mkv tcv (Assert i a e) = Assert i (simplifyIn tenv kv mkv tcv a) e
simplifyAsserts' _ _ _ _ e = e

simplifyIn :: TypeEnv -> KnownValues -> ModifiedKnownValues -> TCValues -> Expr -> Expr
simplifyIn tenv kv mkv tcv e =
    -- simplifyIn' tenv kv mkv e
    let
        e' = simplifyIn' tenv kv mkv tcv e
    in
    if e == e' then e else simplifyIn tenv kv mkv tcv e'

simplifyIn' :: TypeEnv -> KnownValues -> ModifiedKnownValues -> TCValues -> Expr -> Expr
simplifyIn' tenv kv mkv tcv = elimAnds tenv kv mkv . elimLHPP tenv kv tcv . varBetaReduction

elimAnds :: TypeEnv -> KnownValues -> ModifiedKnownValues -> Expr -> Expr
elimAnds tenv kv mkv = elimCalls2 (andFunc mkv) (mkTrue kv tenv)

elimLHPP :: TypeEnv -> KnownValues -> TCValues -> Expr -> Expr
elimLHPP tenv kv tcv a@(App e e') =
    if isRedundantNestedLHPP kv tcv a then mkTrue kv tenv else App (modifyAppRHS (elimLHPP tenv kv tcv) e) (elimLHPP tenv kv tcv e')
elimLHPP tenv kv tcv e = modifyChildren (elimLHPP tenv kv tcv) e

-- We skip checking the outermost arg, which is always the type the lhPP
-- function is walking over
isRedundantNestedLHPP :: KnownValues -> TCValues -> Expr -> Bool
isRedundantNestedLHPP kv tcv (App e _) = isRedundantNestedLHPP' kv tcv e
isRedundantNestedLHPP _ _ e = False

isRedundantNestedLHPP' :: KnownValues -> TCValues -> Expr -> Bool
isRedundantNestedLHPP' _ tcv (Var (Id n _)) = n == lhPP tcv 
isRedundantNestedLHPP' kv tcv a@(App e e') =
    let
        red1 = isRedundantNestedLHPP' kv tcv e
        red2 = isRedundantArg kv tcv e'
    in
    red1 && red2
isRedundantNestedLHPP' _ _ _ = False

isRedundantArg :: KnownValues -> TCValues -> Expr -> Bool
isRedundantArg _ tcv (Type _) = True
isRedundantArg _ tcv e@(Var (Id _ (TyConApp n _))) = n == lhTC tcv
isRedundantArg kv _ l@(Lam _ _) = isIdentity kv l
-- isRedundantArg kv tcv a@(App _ _) = isRedundantNestedLHPP kv tcv a
isRedundantArg _ _ e = trace (show e) False

isIdentity :: KnownValues -> Expr -> Bool
isIdentity kv (Lam _ (Data (DataCon n _ _))) = n == dcTrue kv
isIdentity _ e = False

-- | elimCalls2
-- If one of the arguments to a function with name f with 2 arguments is a,
-- replaces the function call with the other arg
elimCalls2 :: Name -> Expr -> Expr -> Expr
elimCalls2 n e = modify (elimCalls2' n e)

elimCalls2' :: Name -> Expr -> Expr -> Expr
elimCalls2' f a e
    | App (App (Var f') r) a' <- e
    , f == idName f'
    , a == a' = r
    |  App (App (Var f') a') r <- e
    , f == idName f'
    , a == a' = r 
    | otherwise = e