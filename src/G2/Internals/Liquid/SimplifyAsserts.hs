{-# LANGUAGE FlexibleContexts #-}

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
simplifyIn' tenv kv mkv tcv = elimAnds tenv kv mkv . elimLHPP tenv kv tcv . varBetaReduction

elimAnds :: TypeEnv -> KnownValues -> ModifiedKnownValues -> Expr -> Expr
elimAnds tenv kv mkv = elimCalls2 (andFunc mkv) (mkTrue kv tenv)

elimLHPP :: TypeEnv -> KnownValues -> TCValues -> Expr -> Expr
elimLHPP tenv kv tcv a@(App e e') =
    case isNestedLPP tcv a of
        True -> case isRedundantNestedArg kv tcv a of
                    True -> mkTrue kv tenv
                    False -> App (modifyAppRHS (elimLHPP tenv kv tcv) e) (elimLHPP tenv kv tcv e')
        False -> modifyChildren (elimLHPP tenv kv tcv) a
elimLHPP tenv kv tcv e = modifyChildren (elimLHPP tenv kv tcv) e

isNestedLPP :: TCValues -> Expr -> Bool
isNestedLPP tcv (Var (Id n _)) = n == lhPP tcv 
isNestedLPP tcv (App e _) = isNestedLPP tcv e
isNestedLPP _ _ = False

isNestedLHTC :: TCValues -> Expr -> Bool
isNestedLHTC tcv (Var (Id _ (TyConApp n _))) = n == lhTC tcv 
isNestedLHTC tcv (App e _) = isNestedLHTC tcv e
isNestedLHTC _ _ = False

-- We skip checking the outermost arg, which is always the type the lhPP
-- function is walking over
isRedundantNestedArg :: KnownValues -> TCValues -> Expr -> Bool
isRedundantNestedArg kv tcv (App e _) = isRedundantNestedArg' kv tcv e
isRedundantNestedArg _ _ _ = False

isRedundantNestedArg' :: KnownValues -> TCValues -> Expr -> Bool
isRedundantNestedArg' _ tcv (Var (Id n _)) = n == lhPP tcv 
isRedundantNestedArg' kv tcv (App e e') = isRedundantNestedArg' kv tcv e && isRedundantArg kv tcv e'
isRedundantNestedArg' _ _ _ = False

isRedundantArg :: KnownValues -> TCValues -> Expr -> Bool
isRedundantArg _ _ (Type _) = True
isRedundantArg _ tcv (Var (Id _ (TyConApp n _))) = n == lhTC tcv
isRedundantArg kv _ l@(Lam _ _) = isIdentity kv l
isRedundantArg _ tcv a@(App _ _) = isNestedLHTC tcv a
isRedundantArg _ _ _ = False

isIdentity :: KnownValues -> Expr -> Bool
isIdentity kv (Lam _ (Data (DataCon n _ _))) = n == dcTrue kv
isIdentity _ _ = False

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