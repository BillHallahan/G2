{-# LANGUAGE FlexibleContexts #-}

module G2.Internals.Liquid.SimplifyAsserts (simplifyAsserts) where

import G2.Internals.Language
import G2.Internals.Language.KnownValues

import Debug.Trace

type ModifiedKnownValues = KnownValues

simplifyAsserts :: ModifiedKnownValues -> State -> State
simplifyAsserts mkv s@(State {type_env = tenv, known_values = kv}) =
    modifyASTs (simplifyAsserts' tenv kv mkv) s

simplifyAsserts' :: TypeEnv -> KnownValues -> ModifiedKnownValues -> Expr -> Expr
simplifyAsserts' tenv kv mkv (Assume a e) = Assume (simplifyIn tenv kv mkv a) e
simplifyAsserts' tenv kv mkv (Assert i a e) = Assert i (simplifyIn tenv kv mkv a) e
simplifyAsserts' _ _ _ e = e

simplifyIn :: TypeEnv -> KnownValues -> ModifiedKnownValues -> Expr -> Expr
simplifyIn tenv kv mkv e =
    -- simplifyIn' tenv kv mkv e
    let
        e' = simplifyIn' tenv kv mkv e
    in
    if e == e' then e else simplifyIn tenv kv mkv e'

simplifyIn' :: TypeEnv -> KnownValues -> ModifiedKnownValues -> Expr -> Expr
simplifyIn' tenv kv mkv = elimAnds tenv kv mkv . varBetaReduction

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