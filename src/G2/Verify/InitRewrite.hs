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

initRule :: State t -> Bindings -> RewriteRule -> (State t, Id, Bindings)
initRule s@(State { known_values = kv, type_classes = tc }) b r =
    let
        (eenv', tv_env') = updateExprEnvAndTyVarEnv (ru_bndrs r) (expr_env s) (tyvar_env s)

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

        -- Get the RHS
        rhs_expr = ru_rhs r

        -- Equate LHS and RHS
        ret_type = returnType $ typeOf tv_env' lhs_expr
        m_eq_dict = typeClassInst tc HM.empty (KV.eqTC kv) ret_type

        (comp_n, ng') = freshSeededString "comp" (name_gen b)
    in
    case m_eq_dict of
        Just eq_dict ->
            let
                comp = mkApp [Var (Id (KV.eqFunc kv) TyUnknown)
                             , Type ret_type
                             , eq_dict
                             , lhs_expr
                             , rhs_expr]
                eenv'' = E.insert comp_n comp eenv'
            in
            (s { curr_expr = CurrExpr Evaluate comp
               , expr_env = eenv''
               , tyvar_env = tv_env' }
            , Id comp_n (typeOf tv_env' comp)
            , b { name_gen = ng' })
        Nothing -> error "No equality typeclass found"