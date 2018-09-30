{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module G2.Internals.Liquid.SimplifyAsserts ( simplifyAsserts
                                           , simplifyAssertsG) where

import G2.Internals.Language
import G2.Internals.Language.KnownValues
import G2.Internals.Liquid.TCValues

type ModifiedKnownValues = KnownValues

simplifyAsserts :: ASTContainer t Expr => ModifiedKnownValues -> TCValues -> State t -> State t
simplifyAsserts mkv tcv s@(State {type_env = tenv, known_values = kv}) =
    modifyASTs (simplifyAsserts' tenv kv mkv tcv) s

simplifyAssertsG :: ASTContainer m Expr => KnownValues -> TCValues -> TypeEnv -> KnownValues -> m -> m
simplifyAssertsG mkv tcv tenv kv = modifyASTs (simplifyIn tenv kv mkv tcv)

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
simplifyIn' tenv kv mkv _ = elimAnds tenv kv mkv . varBetaReduction


elimAnds :: TypeEnv -> KnownValues -> ModifiedKnownValues -> Expr -> Expr
elimAnds tenv kv mkv = elimCalls2 (andFunc mkv) (mkTrue kv tenv)

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

