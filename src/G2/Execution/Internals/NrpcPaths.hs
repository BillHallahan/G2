{-# LANGUAGE FlexibleContexts, PatternSynonyms #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}

module G2.Execution.Internals.NrpcPaths 
    (
        ReachabilityTable,
        paths,
        reachabilityCheck
    ) where

import qualified Control.Monad.State as SM
import qualified Data.HashSet as HS
import qualified Data.HashMap.Lazy as HM
import G2.Language
import qualified G2.Language.ExprEnv as E
import qualified G2.Language.PathConds as PC
import G2.Solver

import Debug.Trace

type ReachabilityTable = HM.HashMap Name Bool

paths :: Solver solver => HS.HashSet Name -> HS.HashSet Name -> Expr -> Expr -> State t -> Bindings -> solver -> ReachabilityTable -> IO (Int, ReachabilityTable)
paths seen_funcs sym_names nrpc_e_lhs nrpc_e_rhs
        s@(State {expr_env = eenv, path_conds = originalPc})
        bindings@(Bindings {name_gen= ng})
        solver
        table
    -- Variables
    | Var (Id n _) <- nrpc_e_lhs
    , Just e <- E.lookup n eenv = trace("I am in Var")paths seen_funcs sym_names e nrpc_e_rhs s bindings solver table
    | Var (Id n _) <- nrpc_e_lhs
    , E.isSymbolic n eenv || n `elem` sym_names = trace("I am in Var symbolic")return (1, table)
    | Tick _ e <- nrpc_e_lhs = paths seen_funcs sym_names e nrpc_e_rhs s bindings solver table
    -- Function applications 
    | App _ _ <- nrpc_e_lhs = trace("I ma in App")evalPathsForApp seen_funcs sym_names nrpc_e_lhs nrpc_e_rhs s bindings solver table
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

        in paths seen_funcs sym_names e'' nrpc_e_rhs (s {expr_env = eenv'}) (bindings {name_gen = ng'}) solver table
    -- Case expression reaches any assert or error
    | Case {} <- nrpc_e_lhs = evalCasePaths seen_funcs sym_names nrpc_e_lhs nrpc_e_rhs s bindings solver table
    -- Data Constructor
    | Data {} : _ <- unApp nrpc_e_lhs = evalDataConPaths nrpc_e_lhs nrpc_e_rhs s table
    -- Literal
    | l1@(Lit _) <- nrpc_e_lhs = do
        let new_pc_expr = mkApp [Prim Eq TyUnknown, l1, nrpc_e_rhs] 
            new_pc = PC.insert (PC.ExtCond new_pc_expr True) originalPc
            s' = s {path_conds = new_pc}
        r <- solve solver s' bindings (E.symbolicIds . expr_env $ s') (path_conds s')
        case r of
            SAT _ -> return (1, table)
            _ ->  return (0, table)
    | otherwise = error $ "paths: expr not allowed \n" ++ show nrpc_e_lhs

evalPathsForApp :: Solver solver => HS.HashSet Name 
            -> HS.HashSet Name 
            -> Expr 
            -> Expr 
            -> State t 
            -> Bindings 
            -> solver -> ReachabilityTable -> IO (Int, ReachabilityTable)
evalPathsForApp seen_funcs sym_names lhs_e rhs_e 
        s@(State {expr_env = eenv})
        bindings@(Bindings {name_gen= ng})
        solver
        table
        | (Tick _ e1) : es <- unApp lhs_e = paths seen_funcs sym_names (mkApp (e1:es)) rhs_e s bindings solver table
        -- Lambda Function application
        | l@((Lam _ i e) : e2) <- unApp lhs_e = let
            old = idName i
            (x', ng') = freshSeededName old ng
            e1' = renameExpr old x' e
            eenv' = if null e2 then eenv else E.insert x' (head e2) eenv
        in
            trace("I am in lambda") paths seen_funcs sym_names (mkApp (e1': tail e2)) rhs_e (s {expr_env = eenv'}) (bindings {name_gen = ng'}) solver table
        -- Function applications that are not symbolic
        | Var (Id n _) : es <- unApp lhs_e
        , Just e <- E.lookup n eenv
        , not (E.isSymbolic n eenv) = if not (HS.member n seen_funcs) 
            then paths (HS.insert n seen_funcs) sym_names (mkApp (e:es)) rhs_e s bindings solver table
            else return (1, table)
        | Prim _ _ : es <- unApp lhs_e = evalPrimPaths es s bindings seen_funcs sym_names solver table
        -- Symbolic Functions
        | Var (Id n _) : _ <- unApp lhs_e
        ,  E.isSymbolic n eenv = return (1, table)
        -- Data constructor application
        | Data {} : _ <- unApp lhs_e = evalDataConPaths lhs_e rhs_e s table
        | otherwise = error $ "evalPathsForApp: app not allowed \n" ++ show lhs_e

evalCasePaths :: Solver solver => HS.HashSet Name 
            -> HS.HashSet Name 
            -> Expr 
            -> Expr 
            -> State t 
            -> Bindings 
            -> solver -> ReachabilityTable -> IO (Int, ReachabilityTable)
evalCasePaths seen_funcs sym_names lhs_e rhs_e 
        s@(State {expr_env = eenv, tyvar_env = tvnv})
        bindings@(Bindings {name_gen= ng})
        solver
        table
        -- Case expression reaches any assert or error
        | Case {} <- lhs_e
        , (b, table') <- reachabilityCheck HS.empty ng eenv lhs_e table
        , b = trace("I am in case reach") return (0, table')
        -- Case expression where scrutinee is a symbolic variable
        | Case (Var (Id n _)) i _ alts <- lhs_e
        , Just n' <- E.deepLookupVar n eenv
        , E.isSymbolic n' eenv || elem n sym_names = do
            let altExprs = map altExpr alts
                altMatches = map altMatch alts
                sym_vars = concatMap (\case DataAlt _ vrs -> vrs; _ -> []) altMatches
                sym_vars_names = map (\ (Id nn _) -> nn) (i:sym_vars)
                sym_vars_set = HS.union sym_names (HS.fromList sym_vars_names)
            (num_path_alts, table'') <- trace("Sym_var set:" ++ show sym_vars_set)evalAlts altExprs rhs_e s bindings seen_funcs sym_vars_set solver table
            -- num_of_paths <- mapM (\ e' -> paths seen_funcs sym_vars_set e' rhs_e s bindings solver table) altExprs
            -- let count = sum num_of_paths
            trace ("I am in case Var") return (num_path_alts, table'')
        -- Case where scrutinee could be anything, a variable, func application etc.
        | Case e _ _ alts <- lhs_e = do
            let e_ty = typeOf tvnv e
                (new_sym, ng') = freshSeededName (Name "sym" Nothing 0 Nothing) ng
                new_sym_id = Id new_sym e_ty
                eenv' = E.insertSymbolic new_sym_id eenv
                altExprs = map altExpr alts
            (num_path_scrutinee, table') <- paths seen_funcs sym_names e (Var new_sym_id) (s {expr_env = eenv'}) (bindings {name_gen = ng'}) solver table
            (num_path_alts, table'') <- evalAlts altExprs rhs_e s bindings seen_funcs sym_names solver table'
            trace("I am in case all" ) return (num_path_scrutinee * num_path_alts, table'')
        | otherwise = error $ "evalCasePaths: case not allowed \n" ++ show lhs_e

        where
            evalAlts [] _ _ _ _ _ _ tbl = return (0, tbl)
            evalAlts (a:as) r_e s' b' seen sym_n sol tbl = do
                (p, tbl') <- paths seen sym_n a r_e s' b' sol tbl
                (p', tbl'') <- evalAlts as r_e s' b' seen sym_n sol tbl'
                return (p + p', tbl'')

evalDataConPaths :: Expr -> Expr -> State t -> ReachabilityTable -> IO (Int, ReachabilityTable)
evalDataConPaths lhs_e rhs_e s@(State {expr_env = eenv}) table
        -- Data Constructor
        | Data (DataCon n1 _ _ _) : _ <- unApp lhs_e
        , Data (DataCon n2 _ _ _) : _ <- unApp rhs_e = do if n1 == n2 then return (1, table) else return (0, table)
        -- when left is data con but right hand side is symbolic variable
        | (Data _) : _ <- unApp lhs_e
        , Var (Id n _) : _ <- unApp rhs_e
        , E.isSymbolic n eenv = return (1, table)
        -- To catch other data con cases
        | (Data _) : _ <- unApp lhs_e = return (0, table)
        | otherwise = error $ "evalDataConPaths: DataCon application not allowed \n" ++ show lhs_e


evalPrimPaths :: Solver solver => [Expr] -> State t -> Bindings 
            -> HS.HashSet Name 
            -> HS.HashSet Name 
            -> solver -> ReachabilityTable -> IO (Int, ReachabilityTable)
evalPrimPaths [] _ _ _ _ _ tbl= return (0, tbl)
evalPrimPaths (a:as) 
    s@State{expr_env = eenv, tyvar_env = tvnv} 
    b@Bindings{name_gen = ng} seen_funcs sym_names solver table = 
    do 
        let (i, eenv', ng') = createSymVar (typeOf tvnv a) ng eenv
            s' = s {expr_env = eenv'}
            b' = b {name_gen = ng'}
        (a_path, table') <- paths seen_funcs sym_names a (Var i) s' b' solver table
        (as_paths, table'') <- evalPrimPaths as s' b' seen_funcs sym_names solver table'
        return (a_path + as_paths, table'')

createSymVar :: Type -> NameGen -> ExprEnv -> (Id, ExprEnv, NameGen)
createSymVar t ng eenv= 
    let (new_sym, ng') = freshSeededName (Name "sym" Nothing 0 Nothing) ng
        new_sym_id = Id new_sym t
        eenv' = E.insertSymbolic new_sym_id eenv
    in (new_sym_id, eenv', ng')

reachabilityCheck :: HS.HashSet Name -> NameGen -> ExprEnv -> Expr -> ReachabilityTable -> (Bool, ReachabilityTable)
reachabilityCheck seen ng eenv e table = 
    let 
        (res, table') = SM.runState (reachabilityCheck' seen ng eenv e) table 
    in (res, table')

reachabilityCheck' :: SM.MonadState ReachabilityTable m => HS.HashSet Name -> NameGen -> ExprEnv -> Expr -> m Bool
reachabilityCheck' seen ng eenv e
    | Var (Id n _) <- e = 
        do
            curr_tbl <- SM.get
            case HM.lookup n curr_tbl of
                Just b -> return b
                Nothing | (nameOcc n == "assert") || (nameOcc n == "error") -> return True
                Nothing | HS.member n seen -> do
                    SM.modify (HM.insert n False)
                    return False
                Nothing | Just e' <- E.lookup n eenv -> do
                    res <- reachabilityCheck' (HS.insert n seen) ng eenv e'
                    SM.modify (HM.insert n res)
                    return res
                _ -> do
                    SM.modify (HM.insert n False)
                    return False
    | Case e' _ _ alts <- e =  do 
        let altExprs = map altExpr alts
        scrutinee <- reachabilityCheck' seen ng eenv e'
        altsCheck <- mapM (reachabilityCheck' seen ng eenv) altExprs
        return (scrutinee || or altsCheck)
    | App (Lam _ i e1) e2 <- e = do
        let old = idName i
            (x', ng') = freshSeededName old ng
            e1' = renameExpr old x' e1
            eenv' = E.insert x' e2 eenv
        reachabilityCheck' seen ng' eenv' e1'
    | App e1 e2 <- e = do
        res1 <- reachabilityCheck' seen ng eenv e1 
        res2 <- reachabilityCheck' seen ng eenv e2
        return (res1 || res2)
    | Lam _ _ e' <- e = reachabilityCheck' seen ng eenv e'
    | Let b e' <- e =  
        let
            (binds_lhs, binds_rhs) = unzip b

            olds = map idName binds_lhs
            (news, ng') = freshSeededNames olds ng

            e'' = renameExprs (zip olds news) e'
            binds_rhs' = renameExprs (zip olds news) binds_rhs
            eenv' = E.insertExprs (zip news binds_rhs') eenv
        in reachabilityCheck' seen ng' eenv' e''
    | otherwise = return False

