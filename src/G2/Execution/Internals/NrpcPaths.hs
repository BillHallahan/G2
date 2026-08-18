{-# LANGUAGE FlexibleContexts, PatternSynonyms #-}
{-# LANGUAGE OverloadedStrings #-}

module G2.Execution.Internals.NrpcPaths 
    (
        paths,
        reachabilityCheck
    ) where

import qualified Data.HashSet as HS
import G2.Language
import qualified G2.Language.ExprEnv as E
import qualified G2.Language.PathConds as PC
import G2.Solver

paths :: Solver solver => Expr -> Expr -> State t -> Bindings -> solver -> IO Int
paths nrpc_e_lhs nrpc_e_rhs
        s@(State {expr_env = eenv, path_conds = originalPc})
        bindings@(Bindings {name_gen= ng})
        solver 
    | App (Lam _ i e) e2 <- nrpc_e_lhs = let
            old = idName i
            (x', ng') = freshSeededName old ng
            e1' = renameExpr old x' e
            eenv' = E.insert x' e2 eenv
        in 
            paths e1' nrpc_e_rhs (s {expr_env = eenv'}) (bindings {name_gen = ng'}) solver
    | Var (Id n _) : es <- unApp nrpc_e_lhs
    , Just e <- E.lookup n eenv = paths (mkApp (e:es)) nrpc_e_rhs s bindings solver
    | Let b e' <- nrpc_e_lhs =
        -- TO-DO: move it to a function. This is adding redundant code.
        let 
            (binds_lhs, binds_rhs) = unzip b

            olds = map idName binds_lhs
            (news, ng') = freshSeededNames olds ng

            e'' = renameExprs (zip olds news) e'
            binds_rhs' = renameExprs (zip olds news) binds_rhs

            eenv' = E.insertExprs (zip news binds_rhs') eenv

        in paths e'' nrpc_e_rhs (s {expr_env = eenv'}) (bindings {name_gen = ng'}) solver
    | Case (Var (Id n _)) _ _ alts <- nrpc_e_lhs
    , reachabilityCheck HS.empty ng eenv nrpc_e_lhs
    , Just n' <- E.deepLookupVar n eenv
    , E.isSymbolic n' eenv = do
        let altExprs = map altExpr alts
        num_of_paths <- mapM (\ e' -> paths e' nrpc_e_rhs s bindings solver) altExprs
        let count = sum num_of_paths
        return count
    | Case _ _ _ _ <- nrpc_e_lhs = return 1
    | Data (DataCon n1 _ _ _) <- nrpc_e_lhs
    , Data (DataCon n2 _ _ _) <- nrpc_e_rhs = do if n1 == n2 then return 1 else return 0
    | Data _ <- nrpc_e_lhs = return 0
    | l1@(Lit _) <- nrpc_e_lhs = do
        let new_pc_expr = mkApp [Prim Eq TyUnknown, l1, nrpc_e_rhs] 
            new_pc = PC.insert (PC.ExtCond new_pc_expr True) originalPc
            s' = s {path_conds = new_pc}
        r <- solve solver s' bindings (E.symbolicIds . expr_env $ s') (path_conds s')
        case r of
            SAT _ -> return 1
            _ -> return 0
    | otherwise = error $ "paths: expr not allowed \n" ++ show nrpc_e_lhs


reachabilityCheck :: HS.HashSet Name -> NameGen -> ExprEnv -> Expr ->  Bool
reachabilityCheck seen ng eenv e
    | Var (Id n _) <- e
    , (nameOcc n == "assert") || (nameOcc n == "error") = True
    | Var (Id n _) <- e,
    HS.member n seen = False
    | Var (Id n _) <- e
    , Just e' <- E.lookup n eenv = reachabilityCheck (HS.insert n seen) ng eenv e'
    | Case e' _ _ alts <- e = let altExprs = map altExpr alts
                        in reachabilityCheck seen ng eenv e' || any (reachabilityCheck seen ng eenv) altExprs
    | App (Lam _ i e1) e2 <- e = let
            old = idName i
            (x', ng') = freshSeededName old ng
            e1' = renameExpr old x' e1
            eenv' = E.insert x' e2 eenv
        in 
            reachabilityCheck seen ng' eenv' e1'
    | App e1 e2 <- e = reachabilityCheck seen ng eenv e1 || reachabilityCheck seen ng eenv e2
    | Lam _ _ e' <- e = reachabilityCheck seen ng eenv e'
    | Let b e' <- e =  
        let
            (binds_lhs, binds_rhs) = unzip b

            olds = map idName binds_lhs
            (news, ng') = freshSeededNames olds ng

            e'' = renameExprs (zip olds news) e'
            binds_rhs' = renameExprs (zip olds news) binds_rhs
            eenv' = E.insertExprs (zip news binds_rhs') eenv
        in reachabilityCheck seen ng' eenv' e''
    | otherwise = False

