{-# LANGUAGE FlexibleContexts, PatternSynonyms #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}

module G2.Execution.Internals.NrpcPaths 
    (
        ReachabilityTable,
        paths,
        reachabilityCheck,
        getUpdatedStateIfPathsChanged,
        nrpcThreshold
    ) where

import qualified Control.Monad.State as SM
import qualified Data.HashSet as HS
import qualified Data.HashMap.Lazy as HM
import G2.Language
import qualified G2.Language.ExprEnv as E
import qualified G2.Language.PathConds as PC
import qualified G2.Language.Stack as S
import G2.Solver

-- | paths functions under-approximates the number of paths an expression can branch into.
-- Before adding a non-reduced path constraint, paths checks if the expression can branch into more
-- than a threshold number of paths. If it can, then the non-reduced path constraint is 
-- added to the NRPC set of state.
-- For example consider the following case expression:
-- case sym of
-- [] -> some_expr
-- _  -> some_other_expr
-- sym is a symbolic variable, so, we know it will branch into at least 2 paths.
-- In paths functios, nrpc_e_lhs is the left hand side of the non-reduced-path constraint, 
-- which is the case expression from above example, and nrpc_e_rhs is the right hand side of the non-reduced path constraint.
-- Whenever an NRPC should be added for the first time, LHS is always going to be a symbolic variable.
paths :: Solver solver => HS.HashSet Name -> Expr -> Expr -> State t -> Bindings -> solver -> ReachabilityTable -> IO (Int, ReachabilityTable)
paths seen_funcs nrpc_e_lhs nrpc_e_rhs
        s@(State {expr_env = eenv, path_conds = originalPc})
        bindings@(Bindings {name_gen= ng})
        solver
        table
    -- Variables
    | Var (Id n _) <- nrpc_e_lhs
    , E.isSymbolic n eenv = return (1, table)
    | Var (Id n _) <- nrpc_e_lhs
    , Just e <- E.lookup n eenv = paths seen_funcs e nrpc_e_rhs s bindings solver table
    | Tick _ e <- nrpc_e_lhs = paths seen_funcs e nrpc_e_rhs s bindings solver table
    -- Function applications 
    | App _ _ <- nrpc_e_lhs = evalPathsForApp seen_funcs nrpc_e_lhs nrpc_e_rhs s bindings solver table
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

        in paths seen_funcs e'' nrpc_e_rhs (s {expr_env = eenv'}) (bindings {name_gen = ng'}) solver table
    -- Case expression
    | Case {} <- nrpc_e_lhs = evalCasePaths seen_funcs nrpc_e_lhs nrpc_e_rhs s bindings solver table
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
            _ -> return (0, table)
    | SymGen _ _ <- nrpc_e_lhs = return (1, table)
    | Assume _ e1 e2 <- nrpc_e_lhs = do
        paths_e1 <- paths seen_funcs e1 nrpc_e_rhs s bindings solver table
        paths_e2 <- paths seen_funcs e2 nrpc_e_rhs s bindings solver table
        return $ Prelude.max paths_e1 paths_e2
    | otherwise = error $ "paths: expression not allowed \n" ++ show nrpc_e_lhs

evalPathsForApp :: Solver solver => HS.HashSet Name 
            -> Expr 
            -> Expr 
            -> State t 
            -> Bindings 
            -> solver -> ReachabilityTable -> IO (Int, ReachabilityTable)
evalPathsForApp seen_funcs lhs_e rhs_e 
        s@(State {expr_env = eenv})
        bindings@(Bindings {name_gen= ng})
        solver
        table
        | (Tick _ e1) : es <- unApp lhs_e = paths seen_funcs (mkApp (e1:es)) rhs_e s bindings solver table
        | [Lam _ _ e] <- unApp lhs_e = paths seen_funcs e rhs_e s bindings solver table
        -- Lambda Function application
        | (Lam _ i e) : e1 : e2 <- unApp lhs_e = let
            old = idName i
            (x', ng') = freshSeededName old ng
            e1' = renameExpr old x' e
            eenv' = E.insert x' e1 eenv
        in
            evalPathsForApp seen_funcs (mkApp (e1':e2)) rhs_e (s {expr_env = eenv'}) (bindings {name_gen = ng'}) solver table
        -- Function applications that are not symbolic
        | Var (Id n _) : es <- unApp lhs_e
        , Just e <- E.lookup n eenv
        , not (E.isSymbolic n eenv) = if not (HS.member n seen_funcs) 
            then paths (HS.insert n seen_funcs) (mkApp (e:es)) rhs_e s bindings solver table
            else return (1, table)
        | Prim _ _ : _ <- unApp lhs_e = return (1, table)
        -- Symbolic Functions
        | Var (Id n _) : _ <- unApp lhs_e
        ,  E.isSymbolic n eenv = return (1, table)
        -- Data constructor application
        | Data {} : _ <- unApp lhs_e = evalDataConPaths lhs_e rhs_e s table
        | otherwise = return (1, table)

evalCasePaths :: Solver solver => HS.HashSet Name 
            -> Expr 
            -> Expr 
            -> State t 
            -> Bindings 
            -> solver -> ReachabilityTable -> IO (Int, ReachabilityTable)
evalCasePaths seen_funcs lhs_e rhs_e 
        s@(State {expr_env = eenv, tyvar_env = tvnv})
        bindings@(Bindings {name_gen= ng})
        solver
        table
        -- Case expression reaches any assert or error
        | Case {} <- lhs_e
        , (b, table') <- reachabilityCheck HS.empty ng eenv lhs_e table
        , b = return (0, table')
        -- Case expression where scrutinee is a symbolic variable
        | Case (Var (Id n _)) i _ alts <- lhs_e
        , Just n' <- E.deepLookupVar n eenv
        , E.isSymbolic n' eenv = do
            let altExprs = map altExpr alts
                altMatches = map altMatch alts
                sym_vars = concatMap (\case DataAlt _ vrs -> vrs; _ -> []) altMatches
                
                eenv' = foldl (\ en id' -> E.insertSymbolic id' en ) eenv (i:sym_vars)

            (num_path_alts, table'') <- evalAlts altExprs rhs_e s{expr_env = eenv'} bindings seen_funcs solver table
            
            return (num_path_alts, table'')
        -- Case where scrutinee could be anything, a variable, func application etc.
        --
        -- If a case expression's scrutinee branches in m paths and alternatives branch in n paths,
        -- then the total number of paths is m * n.
        -- For example, consider the following case expression:
        --
        -- case (f x) of
        --  [] -> some_expr
        --  _  -> some_other_expr
        -- 
        -- if (f x) branches into 10 paths, some_expr branches into 5 paths, and 
        -- some_other_expr branches into 3 paths, then the total number of paths is 10 * (5 + 3) = 80.
        -- It looks like an over-approximation but it is still an under-approximation because of how paths work. 
        -- Paths underapproximate function application, and since, we check approximate number of paths
        -- an alternatives expression can generate, there is a chance that we are 
        -- under-approximating the number of paths in the alternatives expression.
        -- 
        | Case e i _ alts <- lhs_e = do
            let e_ty = typeOf tvnv e
                (new_sym, ng') = freshSeededName (Name "sym" Nothing 0 Nothing) ng
                new_sym_id = Id new_sym e_ty
                altExprs = map altExpr alts
                altMatches = map altMatch alts
                sym_vars = concatMap (\case DataAlt _ vrs -> vrs; _ -> []) altMatches

                eenv' = foldl (\ en id' -> E.insertSymbolic id' en ) eenv (i:new_sym_id:sym_vars)

            (num_path_scrutinee, table') <- paths seen_funcs e (Var new_sym_id) s (bindings {name_gen = ng'}) solver table
            (num_path_alts, table'') <- evalAlts altExprs rhs_e (s {expr_env = eenv'}) bindings seen_funcs solver table'
            
            return (num_path_scrutinee * num_path_alts, table'')
        | otherwise = error $ "evalCasePaths: case not allowed \n" ++ show lhs_e

        where
            evalAlts [] _ _ _ _ _ tbl = return (0, tbl)
            evalAlts (a:as) r_e s' b' seen sol tbl = do
                (p, tbl') <- paths seen a r_e s' b' sol tbl
                (p', tbl'') <- evalAlts as r_e s' b' seen sol tbl'
                return (p + p', tbl'')

evalDataConPaths :: Expr -> Expr -> State t -> ReachabilityTable -> IO (Int, ReachabilityTable)
evalDataConPaths lhs_e rhs_e s@(State {expr_env = eenv}) table
        -- Data Constructor
        | Data (DataCon n1 _ _ _) : _ <- unApp lhs_e
        , Data (DataCon n2 _ _ _) : _ <- unApp rhs_e = do if n1 == n2 then return (1, table) else return (0, table)
        -- when left is data con but right hand side is symbolic variable
        | Data _ : _ <- unApp lhs_e
        , Var (Id n _) : _ <- unApp rhs_e
        , E.isSymbolic n eenv = return (1, table)
        | Data (DataCon n1 _ _ _) : _ <- unApp lhs_e
        , Var (Id n _) : _ <- unApp rhs_e
        , Just (Data (DataCon n2 _ _ _)) <- E.lookup n eenv
        , n1 == n2 = return (1, table)
        -- To catch other data con cases
        | (Data _) : _ <- unApp lhs_e = return (0, table)
        | otherwise = error $ "evalDataConPaths: DataCon application not allowed \n" ++ show lhs_e

reachabilityCheck :: HS.HashSet Name -> NameGen -> ExprEnv -> Expr -> ReachabilityTable -> (Bool, ReachabilityTable)
reachabilityCheck seen ng eenv e table = SM.runState (reachabilityCheck' seen ng eenv e) table 
   

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

nrpcThreshold :: Int
nrpcThreshold = 1
-- | If a non-reduced path constraint's symbolic variable gets concretized, then it is possible that
-- the number of paths an expression can branch into has changed. Function getUpdatedStateIfPathsChanged
-- checks if path has changed for the given non-reduced path constraint. 
-- If it is not greater than the threshold, then the state is updated to evaluate the non-reduced path constraint.
getUpdatedStateIfPathsChanged :: Solver solver => HS.HashSet Name -> NRPC -> State t -> Bindings -> solver -> IO (State t)
getUpdatedStateIfPathsChanged _ np s@State{expr_env = eenv} b solver = do
    let nrpc_r = nrpc_rhs np
        nrpc_l = nrpc_lhs np
        reach_tbl = reach_table s
        -- Call paths here
    (path, reach_tbl') <- paths HS.empty nrpc_l nrpc_r s b solver reach_tbl
    -- print $ "Number of paths: " ++ show path ++ " for NRPC: " ++ show (E.lookup (idName (fromJust (varId  nrpc_r))) eenv)
    
    let s' = s {reach_table = reach_tbl'} 
     
    if path > nrpcThreshold then return s else updateState np s' 

updateState :: NRPC -> State t -> IO (State t)
updateState np s@(State {curr_expr = c_e
                    , exec_stack = stck}) = do
    let nrpc_r = nrpc_rhs np
        nrpc_l = nrpc_lhs np
        frame = CurrExprFrame (EnsureEq nrpc_l) c_e
        s' = s {
            curr_expr = CurrExpr Evaluate nrpc_r, 
            exec_stack = S.push frame stck,
            non_red_path_conds = deleteNRPC np (non_red_path_conds s)}

    return s'
