{-# LANGUAGE FlexibleContexts, PatternSynonyms #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}

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

paths :: Solver solver => HS.HashSet Name -> HS.HashSet Name -> Expr -> Expr -> State t -> Bindings -> solver -> IO Int
paths seen_funcs sym_names nrpc_e_lhs nrpc_e_rhs
        s@(State {expr_env = eenv, path_conds = originalPc, tyvar_env = tvnv})
        bindings@(Bindings {name_gen= ng})
        solver
    -- Variables
    | Var (Id n _) <- nrpc_e_lhs
    , Just e <- E.lookup n eenv = paths seen_funcs sym_names e nrpc_e_rhs s bindings solver
    | Var (Id n _) <- nrpc_e_lhs
    , n `elem` sym_names = return 1
    -- Lambda function
    | (Lam _ i e) : e2 <- unApp nrpc_e_lhs = let
            old = idName i
            (x', ng') = freshSeededName old ng
            e1' = renameExpr old x' e
            eenv' = if null e2 then eenv else E.insert x' (mkApp e2) eenv
        in
            paths seen_funcs sym_names e1' nrpc_e_rhs (s {expr_env = eenv'}) (bindings {name_gen = ng'}) solver
    | Tick _ e <- nrpc_e_lhs = paths seen_funcs sym_names e nrpc_e_rhs s bindings solver
    | (Tick _ e1) : es <- unApp nrpc_e_lhs = paths seen_funcs sym_names (mkApp (e1:es)) nrpc_e_rhs s bindings solver
    -- Function applications that are not symbolic
    | Var (Id n _) : es <- unApp nrpc_e_lhs
    , Just e <- E.lookup n eenv
    , not (E.isSymbolic n eenv) = if not (HS.member n seen_funcs) 
        then paths seen_funcs sym_names (mkApp (e:es)) nrpc_e_rhs s bindings solver
        else return 1
    -- Symbolic Functions
    | Var (Id n _) : _ <- unApp nrpc_e_lhs
    ,  E.isSymbolic n eenv = return 1
    -- Let expressions
    | Let b e' <- nrpc_e_lhs =
        -- TO-DO: move it to a function. This is adding redundant code.
        let 
            (binds_lhs, binds_rhs) = unzip b

            olds = map idName binds_lhs
            (news, ng') = freshSeededNames olds ng

            e'' = renameExprs (zip olds news) e'
            binds_rhs' = renameExprs (zip olds news) binds_rhs

            eenv' = E.insertExprs (zip news binds_rhs') eenv

        in paths seen_funcs sym_names e'' nrpc_e_rhs (s {expr_env = eenv'}) (bindings {name_gen = ng'}) solver
    -- Case expression where scrutinee is a symbolic variable
    | Case (Var (Id n _)) i _ alts <- nrpc_e_lhs
    , not (reachabilityCheck HS.empty ng eenv nrpc_e_lhs)
    , Just n' <- E.deepLookupVar n eenv
    , E.isSymbolic n' eenv || elem n sym_names = do
        let altExprs = map altExpr alts
            altMatches = map altMatch alts
            sym_vars = concatMap (\case DataAlt _ vrs -> vrs; _ -> []) altMatches
            sym_vars_names = map (\ (Id nn _) -> nn) (i:sym_vars)
            sym_vars_set = HS.union sym_names (HS.fromList sym_vars_names)
        num_of_paths <- mapM (\ e' -> paths seen_funcs sym_vars_set e' nrpc_e_rhs s bindings solver) altExprs
        let count = sum num_of_paths
        return count
    -- Case where scrutinee could be anything, a variable, func application etc.
    | Case e _ _ alts <- nrpc_e_lhs = do
        let e_ty = typeOf tvnv e
            (new_sym, ng') = freshSeededName (Name "sym" Nothing 0 Nothing) ng
            new_sym_id = Id new_sym e_ty
            eenv' = E.insertSymbolic new_sym_id eenv
            altExprs = map altExpr alts
        num_path_scrutinee <- paths seen_funcs sym_names e (Var new_sym_id) (s {expr_env = eenv'}) (bindings {name_gen = ng'}) solver
        num_path_alts <- mapM (\ e' -> paths seen_funcs sym_names e' nrpc_e_rhs s bindings solver) altExprs
        return (num_path_scrutinee * sum num_path_alts)
    -- when left hand side and right hand side expressions of NRPC are Data constructors
    | Data (DataCon n1 _ _ _) : _ <- unApp nrpc_e_lhs
    , Data (DataCon n2 _ _ _) : _ <- unApp nrpc_e_rhs = do if n1 == n2 then return 1 else return 0
    -- when left is data con but right hand side is symbolic variable
    | (Data _) : _ <- unApp nrpc_e_lhs
    , Var (Id n _) : _ <- unApp nrpc_e_rhs
    , E.isSymbolic n eenv = return 1
    -- To catch other data con cases
    | (Data _) : _ <- unApp nrpc_e_lhs = return 0
    -- Literal
    | l1@(Lit _) <- nrpc_e_lhs = do
        let new_pc_expr = mkApp [Prim Eq TyUnknown, l1, nrpc_e_rhs] 
            new_pc = PC.insert (PC.ExtCond new_pc_expr True) originalPc
            s' = s {path_conds = new_pc}
        r <- solve solver s' bindings (E.symbolicIds . expr_env $ s') (path_conds s')
        case r of
            SAT _ -> return 1
            _ ->  return 0
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

