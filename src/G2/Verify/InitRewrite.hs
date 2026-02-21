{-# LANGUAGE OverloadedStrings #-}

module G2.Verify.InitRewrite where

import G2.Equiv.InitRewrite
import G2.Language
import qualified G2.Language.ExprEnv as E
import G2.Language.Naming
import qualified G2.Language.Typing as T
import qualified G2.Language.TyVarEnv as TV
import qualified G2.Language.Expr as X
import qualified G2.Language.KnownValues as KV

import qualified Data.HashMap.Lazy as HM
import Data.List

initRule :: State t -> Bindings -> RewriteRule -> (State t, Id, Bindings)
initRule s@(State { known_values = kv, type_classes = tc }) b r =
    let
        (eenv', tv_env') = updateExprEnvAndTyVarEnv kv (ru_bndrs r) (expr_env s) (tyvar_env s)

        -- make LHS into a single expr
        f_name = ru_head r
        f_maybe = E.lookup f_name (expr_env s)
        
        lhs_expr =
            case f_maybe of
                Nothing -> error "function name not found"
                Just f ->
                    let t = T.typeOf (tyvar_env s) f
                        i = Id f_name t
                        v = Var i
                    in
                    X.mkApp (v:ru_args r)
        (missing, ng') = missingBinders (name_gen b) tv_env' lhs_expr
        lhs_expr' = mkApp $ lhs_expr:map Var missing

        -- Get the RHS
        rhs_expr = mkApp $ ru_rhs r:map Var missing

        -- Equate LHS and RHS
        ret_type = tyVarSubst tv_env' . returnType $ typeOf tv_env' lhs_expr'
        m_eq_dict = typeClassInst tc HM.empty (KV.eqTC kv) ret_type

        (comp_n, ng'') = freshSeededString "comp" ng'
    in
    case m_eq_dict of
        Just eq_dict ->
            let
                comp = mkApp [Var (Id (KV.eqFunc kv) TyUnknown)
                             , Type ret_type
                             , eq_dict
                             , lhs_expr'
                             , rhs_expr]
                eenv'' = E.insert comp_n comp eenv'
                eenv''' = foldl' (flip E.insertSymbolic) eenv'' missing
            in
            (s { curr_expr = CurrExpr Evaluate comp
               , expr_env = eenv'''
               , tyvar_env = tv_env' }
            , Id comp_n (typeOf tv_env' comp)
            , b { name_gen = ng'' })
        Nothing -> error "No equality typeclass found"

updateExprEnvAndTyVarEnv :: KnownValues -> [Id] -> ExprEnv -> TyVarEnv -> (ExprEnv, TyVarEnv)
updateExprEnvAndTyVarEnv kv is eenv tv_env =
    let
        (ty_is, v_is) = partition (hasTYPE . typeOf tv_env) is
    in
    (foldr E.insertSymbolic eenv v_is, foldr (\(Id n _) -> TV.insert n (tyInteger kv)) tv_env ty_is)

missingBinders :: NameGen -> TyVarEnv -> Expr -> ([Id], NameGen)
missingBinders ng tv_env e =
    let
        ts = anonArgumentTypes $ typeOf tv_env e
        (ng', is) = mapAccumL (\ng_ t -> let (n, ng_') = freshName ng_ in (ng_', Id n t)) ng ts
    in
    (is, ng')