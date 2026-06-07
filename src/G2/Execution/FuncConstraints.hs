{-# LANGUAGE BangPatterns, OverloadedStrings #-}

module G2.Execution.FuncConstraints where

import G2.Config
import G2.Execution.PrimitiveEval
import G2.Execution.Reducer
import G2.Language
import qualified G2.Language.ExprEnv as E
import G2.Language.Monad
import qualified G2.Language.PathConds as PC
import qualified G2.Language.Stack as Stck
import G2.Lib.Printers
import G2.Solver

import Control.Monad
import Control.Monad.Extra
import Control.Monad.IO.Class
import qualified Control.Monad.State.Lazy as SM
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import Data.List
import Data.Maybe

import qualified Data.Text as T

-- | A reducer to add higher order functions to the symbolic function constraints for solving later  
addFuncConstraintReducer :: MonadIO m =>
                            Config
                         -> HS.HashSet Name -- ^ Names of variables to not inline when checking syntactic equivalence
                         -> Reducer m Int t
addFuncConstraintReducer config no_inline =
    (mkSimpleReducer (\_ -> 0) (redFuncConstraint no_inline))
        { onAccept = \s b fc_count -> do
            if print_num_nrpc config
                then liftIO . putStrLn $ "Func Constraints Generated: " ++ show fc_count
                else return ()
            return (s, b) }

redFuncConstraint :: Monad m =>
                     HS.HashSet Name -- ^ Names of variables to not inline when checking syntactic equivalence
                  -> RedRules
                     m
                     Int
                     t
redFuncConstraint no_inline fc_count s b =
    case addFuncConstraints no_inline s (name_gen b) of
        Just (s', ng') -> return (Finished, [(s', fc_count + 1)], b { name_gen = ng' })
        Nothing -> return (Finished, [(s, fc_count)], b)

addFuncConstraints :: HS.HashSet Name -- ^ Names of variables to not inline when checking syntactic equivalence
                   -> State t
                   -> NameGen
                   -> Maybe (State t, NameGen)
addFuncConstraints no_inline
                   s@(State { expr_env = eenv
                            , curr_expr = CurrExpr _ ce
                            , sym_func_constraints = sym_fc }) 
                   ng
    |  Var (Id n t):es_ce <- unApp ce
    , isTyFun t
    , E.isSymbolic n eenv =
        let
            (ae, stck') = allApplyFrames (exec_stack s)
            es = es_ce ++ ae

            (ret_id, ng') = freshSeededId (Name "fc_ret" Nothing 0 Nothing) (returnType t) ng
            fc = FC { fc_preconds = []
                    , fc_args = es
                    , fc_ret = Var ret_id }
            
            sym_fc' = addFC n fc sym_fc
            eenv' = E.insertSymbolic ret_id eenv
            s' = s { curr_expr = CurrExpr Return (Var ret_id)
                   , expr_env = eenv'
                   , exec_stack = stck'
                   , sym_func_constraints = sym_fc' }
        in
        Just (s', ng')
    | otherwise = Nothing

allApplyFrames :: Stck.Stack Frame -> ([Expr], Stck.Stack Frame)
allApplyFrames stck = go [] stck stck
    where
        go aes pop_stck stck_top_ups
                    | Just (ApplyFrame ae, stck') <- Stck.pop pop_stck = go (ae:aes) stck' stck'
                    | Just (UpdateFrame _, stck') <- Stck.pop pop_stck = go aes stck' stck_top_ups
                    | otherwise = (reverse aes, stck_top_ups)

    -- | v@(Var (Id n _)):es_ce <- unApp (getExpr s)
    -- , let (ae, stck) = allApplyFrames (exec_stack s)
    -- , let es = es_ce ++ ae
    -- , let ce' = mkApp (v:es)
    -- , Just nrpc@(NRPC { nrpc_rhs = rhs }) <- findNRPC (findSynEq ce') (non_red_path_conds s) =
    --     Just (s { curr_expr = CurrExpr Evaluate rhs, exec_stack = stck }, ng)
    -- where
    --     findSynEq ce_ nrpc = eqUpToTypesInlineIgnoringTicks no_inline (expr_env s) (nrpc_lhs nrpc) ce_
-- getNonRedForHigherOrder no_inline ng s
--     | Just (s', _, _, ng1) <- createNonRed ng Focused s = Just (s', ng1)
--     | otherwise = Nothing

addFC :: Name -> FuncConstraint -> FuncConstraints -> FuncConstraints
addFC n fc = HM.insertWith (++) n [fc]

-- Note [Solving Function Constraints]
-- Function constraints have the forms:
--
--   preconditions => f a1 ... ak = r
--
-- where:
-- * preconditions is a conjunction and disjunction of expressions. These expressions are either equalities/inequalities between integer variables and concrete integers,
--   or applications of predicates to literal arguments 
-- * f is a symbolic function
-- * a1 ... ak are arguments, r is the return value.
--
-- To solve a set of function constraints, we (a) take the following steps 1 to 5 repeatedly and (b) take step (6) if none of these earlier rules apply:
--
-- 1) unfolADTArgs
-- 
--    We check if there is a function f such that the i^th argument x of that function is an ADT that is WHNF in all constraints.
--    If there is, we instantiate this function to branch on that argument. Each of the k branches then calls a corresponding newly generated
--    symbolic function f1...fk. This function is passed all arguments of f EXCEPT for x. Since x has an ADT type, each function is also passed all
--    arguments from the constructor.  The original constraints are then rewritten in terms of f1...fk.
--
--    For example, suppose we have:
--        f (x:xs) 4 = 6
--        f (y:ys) e = 10 -- ^ For some expression e
--        f [] 6 = 22
--        f [] 19 = 25
--    The first argument to each f is in WHNF, so we instantiate f to branch on that argument:
--        f = \y z -> case y of
--                      [] -> f1 z
--                      w:ws -> f2 w ws z
--    We then rewrite the constraints to:
--        f2 x xs 4 = 6
--        f2 y ys e = 10
--        f1 6 = 22
--        f1 19 = 25
--    (Note that this step might be done repeatedly- for example, in the above, we can now split on the first argument of f1)
--
-- 2)
--
--    We look for arguments that are symbolic variables of ADT types. We then instantiate these symbolic variables to case expressions
--    that branch on a fresh integer variable to choose a constructor with fresh symbolic arguments. For example, if we have:
--        f (xs :: [Int]) = 7
--    where xs is symbolic, we introduce a fresh Int n, and instantiate xs to:
--       xs = case n of
--                1 -> []
--                2 -> y:ys -- y, ys fresh symbolic variables
--    We add a path constraint that `1 <= n <= 2`.
--    We then unroll the constraint on f into separate constraints for each possible constructor, with corresponding preconditions.
-- For example, the constraint above becomes:
--        n = 1 => f [] = 7
--        n = 2 => f (y:ys) = 7
--
-- 3)
--
--    We look for arguments that are case constructs introduced in step 2, and do the same translation into a pair of function constraints
--    that we do in (2).  That is, if we have a function constraint:
--        f xs = 7
--    and we already have:
--       xs = case n of
--                1 -> []
--                2 -> y:ys -- y, ys fresh symbolic variables
--    we rewrite the constraint to be:
--        n = 1 => f [] = 7
--        n = 2 => f (y:ys) = 7
--
-- 4)
--
--    We extract all literal arguments into predicate checks.  For each function with literal arguments:
--        f 1# (x:xs) 4# (y :: Int#)
--    we generate a fresh predicate p accepting all literal arguments:
--        p :: Int# -> Int# -> Int# -> Bool
--    We then rewrite f to branch based on applying p to the literal arguments:
--        f a ys b c = case p a b c of
--                         True -> f1 ys
--                         False -> f2 ys
--    And update constraints accordingly:
--        p 1# 4# y => f1 (x:xs)
--        not (p 1# 4# y) => f2 (x:xs)
--
-- 5)
--
--    We check if there are any "variable assignments"- "functions" that have no arguments. If so, we make sure all assignments to the same variable are consistent.
--    For instance, we might reach a point where we have:
--        f7 = x:xs
--        f7 = y:z:zs
--    These can be made consistent by setting `x = y` and `xs = z:zs`.
--
-- If none of steps (1) to (5) apply, we move on to step (6):
--
-- 6)
--
--    Since none of (1) to (5) apply, for each argument of a function f, there must be at least one constraint
--    where that argument is not in WHNF and is not a symbolic variable.  For instance:
--                 f A  B  = 6
--        n = 1 => f C  D  = 2
--        n = 1 => f e1 D  = 5
--        n = 2 => f E  e2 = 10
--        where e1, e2 are non-SWHNF expressions.
-- Here, we cannot branch on any of the arguments via step (2), because e1 blocks branching on the first argument, and e2 blocks branching on the second argument.
-- However, if we knew that either n = 1 or n = 2, then branching would be possible. Thus, we choose one of these constraints, and rewrite f.
-- Suppose we choose `n = 1`.  We instantiate f to be:
--        f x y = case n = 1 of
--                      True -> f2 y -- Notice we exclude the first argument, because it is e1 in one of the constraints when `n = 1`
--                      False -> f3 x y
-- We then rewrite accordingly:
--        n = 1 =>  f2 B  = 6
--        n /= 1 => f3 A B  = 6
--        n = 1 =>  f2 D  = 2
--        n = 1 =>  f2 D  = 5
--        n = 2 =>  f3 E e2 = 10
-- We now return to rules (1) to (3). Notice that we will actually not be able to solve for `n = 1`/f2, because `f2 D = 2` and `f2 D = 5` is a constradiction.
-- However, we will be able to solve for `n = 2` and `f3`.

-- Note [Delaying Step 6]
-- Read Note [Solving Function Constraints] (above) first.
-- A natural question is why we delay step 6 until after none of steps 1 to 4 apply. To answer this, consider:
--        n = 1 => f (x:xs) e1 = 1
--        n = 1 => f []     A  = 2
--        n = 1 => f []     B  = 5
--        n = 2 => f []     B =  3
--        n = 2 => f []     B =  4
-- To solve the above, we must have `n = 1`, otherwise we have `f [] B = 3` and `f [] B = 4`. Notice, though, that if we apply step (4) immediately, we get:
--        f a b = case n = 1 of
--                    True -> f2 a
--                    False -> f3 a b
-- Which gets us new constraints:
--        n = 1 => f2 (x:xs)   = 1
--        n = 1 => f2 []       = 2
--        n = 1 => f2 []       = 5
--        n = 2 => f3 []     B =  3
--        n = 2 => f3 []     B =  4
-- This is now unsatisfiable, because we have `f2 [] = 2` and `f2 [] = 5`. Thus, we instead must branch the function based on list constructor:
--        f a b = case a of
--                    [] -> f3 b
--                    c:ds -> f4 c ds b
--  getting new constraints:
--        n = 1 => f3 e1 = 1
--        n = 1 => f4 A  = 2
--        n = 1 => f4 B  = 5
--        n = 2 => f4 B  = 3
--        n = 2 => f4 B  = 4
-- f3 can now be handled by step (1) and f4 by step (2).

{-
Problem:
If we fail to solve function constraints, have to try and reduce arguments.
This then may introduce more constraints, making the problem actually harder to solve.
Suppose we have two argument e1 and e2. If reducing e2 would have been sufficient to solve the orginal constraints,
but reducing e1 adds a constraint, that is unfortunate!

Possible solution:
- When reducing expressions, assign them a precondition. All generated function constraints have that precondition,
and the constraint can only be used during solving if that precondition is satisfied.
This way, the precondition allows choosing between making use of the argument and having the extra constraint,
or not using the argument and also discarding the constraint.
-}


-- data PreC = Id :== Int
--              | PNot PreC
--              | PAnd [PreC]
--              | POr [PreC]


-- TODO: Shouldn't be returning an empty list of states in the Nothing case
solveFuncConstraintsReducer :: (Solver solver, MonadIO m) => solver -> Reducer m () t
solveFuncConstraintsReducer solver = mkSimpleReducer (\_ -> ()) go
    where
        go _ s b | true_assert s = do
                    r <- solveFuncConstraints solver s (name_gen b)
                    liftIO . putStrLn $ case r of Just _ -> "Just"; Nothing -> "Nothing"
                    case r of
                        Just (s', ng') -> return (Finished, [(s', ())], b { name_gen = ng' })
                        Nothing -> return (Finished, [], b) -- TODO
                 | otherwise = return (Finished, [], b)

data FCRes = SatFC FuncConstraints | UnsatFC deriving Eq

solveFuncConstraints :: (Solver solver, MonadIO m) => solver -> State t -> NameGen -> m (Maybe (State t, NameGen))
solveFuncConstraints solver s@(State { sym_func_constraints = fc }) ng = do
    (r, (s', !ng')) <- runStateNGT (solveFC solver 5 fc) s ng
    return $ case r of
                    SatFC fcs' -> Just (s' { solved_sym_func_constraints = True
                                           , sym_func_constraints = fcs' }, ng')
                    _ -> Nothing

-- TODO: Do we actually need the counter here?
solveFC :: (Solver solver, MonadIO m) => solver -> Int -> FuncConstraints -> StateNGT t m FCRes
solveFC _ 0 _ = return UnsatFC
solveFC solver !n fcs = do
    -- Convert functions with only a single constraint into constants
    -- fcs_nosingle <- return . HM.mapMaybe id =<< HM.traverseWithKey solveSingleton fcs
    let pg = mkPrettyGuide (HM.toList fcs)
    liftIO $ putStrLn $ "fcs =\n" ++ T.unpack (prettyFuncConstraints pg fcs)  

    distinct <- checkDistinct solver fcs

    case distinct of
        True -> return (SatFC fcs)
        False -> do
            fcs_simp_pieces <- concatMapM (uncurry simplifyReturns) $ HM.toList fcs
            let fc_simp_reassembled = HM.fromListWith (++) fcs_simp_pieces

            -- Replace ADT symbolic variables with case expressions
            fcs_replaced_sym_adt <- mapM replaceADTSymVars fc_simp_reassembled

            fcs_precond <- mapM caseToPreCond fcs_replaced_sym_adt
            let pg_precond = updatePrettyGuide (HM.toList fcs_precond) pg
            liftIO $ putStrLn $ "fcs_precond =\n" ++ T.unpack (prettyFuncConstraints pg_precond fcs_precond)  

            -- Introduce branches on ADTs
            fcs_unfold_adt_pieces <- concatMapM (uncurry unfoldADTArgs) $ HM.toList fcs_precond
            let fc_unfold_adt_reassembled = HM.fromListWith (++) fcs_unfold_adt_pieces

            liftIO $ putStrLn "after unfoldADTArgs"
            let pg_assem = updatePrettyGuide (HM.toList fc_unfold_adt_reassembled) pg_precond
            liftIO $ putStrLn $ "fc_reassembled =\n" ++ T.unpack (prettyFuncConstraints pg_assem fc_unfold_adt_reassembled)

            solveFC solver (n - 1) fc_unfold_adt_reassembled

solveSingleton :: Monad m => Name -> [FuncConstraint] -> StateNGT t m (Maybe [FuncConstraint])
solveSingleton _ [] = return Nothing
solveSingleton n [FC { fc_args = as, fc_ret = r }] = do
    tv_env <- tyVarEnv

    lam_is <- freshIdsN (map (typeOf tv_env) as)
    let body = mkLams (zip (repeat TermL) lam_is) $ r
    insertE n body
    return Nothing
solveSingleton _ xs = return $ Just xs

-- | If all function constraints for a particular function return the same constructor,
-- split into separate function constraints for each argument to that constructor
simplifyReturns :: MonadIO m => Name -> [FuncConstraint] -> StateNGT t m [(Name, [FuncConstraint])]
simplifyReturns n fcs = do
    eenv <- exprEnv
    tv_env <- tyVarEnv

    case fcs of
        (fc:_) | -- Check if all return values have the same constructor
                 let r = fc_ret fc
                     rs = map fc_ret fcs
               , Data dc@(DataCon { dc_name = dc_n, dc_type = dc_ty }):_ <- unApp $ inlineVars eenv r
               , all (sameConstructor eenv dc_n) rs -> do
                    -- Set up the original function to return the required data constructor
                    -- with arguments constructed by fresh symbolic functions 
                    let existing_args = map (typeOf tv_env) $ fc_args fc
                    
                    lam_is <- freshIdsN existing_args
                    per_arg_func <- mapM (\t -> do
                                            fn <- freshSeededStringN "sym_f"
                                            let fi = Id fn (mkTyFun $ existing_args ++ [t])
                                            insertSymbolicE fi
                                            return fi
                                         ) $ anonArgumentTypes dc_ty
                    
                    let ret_val = mkApp $ Data dc:map (\f -> (mkApp $ (Var f):map Var lam_is)) per_arg_func
                        func_def = mkLams (zip (repeat TermL) lam_is) ret_val
                    insertE n func_def

                    -- Convert existing function constraints into constraints for the newly created functions
                    let new_fcs = concatMap (\this_fc -> 
                                    case unApp . inlineVars eenv $ fc_ret this_fc of
                                        [] -> error "simplifyReturns: impossible"
                                        (_:ret_p) -> zipWith (\f p -> (idName f, [this_fc { fc_ret = p }])) per_arg_func ret_p
                                    ) fcs

                    return new_fcs

        _ -> return [(n, fcs)]
    where
        sameConstructor eenv dc_n e
                | Data (DataCon { dc_name = dc_n', dc_type = dc_ty }):_ <- unApp $ inlineVars eenv e
                , dc_n == dc_n' = True
                | otherwise = False


replaceADTSymVars :: MonadIO m => [FuncConstraint] -> StateNGT t m [FuncConstraint]
replaceADTSymVars fcs = do
    eenv <- exprEnv
    tenv <- typeEnv
    tv_env <- tyVarEnv

    mapM (\fc -> do 
        mapM_ (go eenv tenv tv_env) (fc_args fc)
        return $ fc) fcs
    where
        go eenv tenv tv_env e
            | Var (Id n t) <- inlineVars eenv e
            , E.isSymbolic n eenv
            , TyCon tn _:_ <- unTyApp $ tyVarSubst tv_env t
            , Just (DataTyCon { data_cons = dcs }) <- HM.lookup tn tenv = do
                branch_n <- freshSeededStringN "n"
                bindee <- freshSeededStringN "bindee"
                let branch_i = Id branch_n TyLitInt
                    branch_var = Var branch_i
                insertSymbolicE branch_i
                insertPCStateNG (ExtCond (mkApp $ [Prim Le TyUnknown, Lit (LitInt 1), Var branch_i]) True)
                insertPCStateNG (ExtCond (mkApp $ [Prim Le TyUnknown, Var branch_i, Lit (LitInt $ genericLength dcs)]) True)

                alts_expr <- mapM (\dc -> do
                                    let ts = anonArgumentTypes (typeOf tv_env dc)
                                    dc_as <- freshIdsN ts
                                    mapM insertSymbolicE dc_as
                                    return . mkApp $ Data dc:map Var dc_as
                            ) dcs
                
                let alts = zipWith Alt (map (LitAlt . LitInt) [1..]) alts_expr
                    cse = Case
                            branch_var
                            (Id bindee TyLitInt)
                            t
                            alts
                insertE n cse

                return ()

            | otherwise = do
                return ()

caseToPreCond :: MonadIO m => [FuncConstraint] -> StateNGT t m [FuncConstraint]
caseToPreCond fcs = concatMapM go fcs
    where
        go fc@(FC { fc_preconds = pre, fc_args = es }) = do
            es' <- mapM getOutCases es
            let case_pats = map getCasePats es'
                m_ind_case_pat = findIndex isJust case_pats
            case m_ind_case_pat of
                Just ind -> do
                    let Just (branch_i, alts) = case_pats !! ind
                        eq i = mkApp $ [Prim Eq TyUnknown, Var branch_i, Lit i]
                    
                    let fc_branch = map (\(lit_v, dc) -> fc { fc_preconds = eq lit_v:pre, fc_args = replaceAt ind dc es'}) alts
                    return fc_branch
                Nothing -> return [fc]
            
            
        getOutCases v@(Var (Id n _)) = do
            eenv <- exprEnv
            let e = inlineVars eenv v
            case e of
                cse@(Case _ _ _ (Alt (LitAlt _) _:_)) -> return cse
                _ -> return v
        getOutCases e = return e

        getCasePats (Case (Var i) (Id _ TyLitInt) _ alts) = Just (i, map (\(Alt (LitAlt l) dc) -> (l, dc)) alts)
        getCasePats _ = Nothing

unfoldADTArgs :: MonadIO m => Name -> [FuncConstraint] -> StateNGT t m [(Name, [FuncConstraint])]
unfoldADTArgs n [] = return []
unfoldADTArgs n fcs@(first_fc:_) = do
    eenv <- exprEnv
    tenv <- typeEnv
    tv_env <- tyVarEnv

    let ret_ty = typeOf tv_env $ fc_ret first_fc

    -- Find an argument that is (1) an ADT where (2) all arguments are data constructor applications
    let matching_args = transpose $ map fc_args fcs
        all_whnf = findIndex (all (isADT . inlineVars eenv)) matching_args
    case all_whnf of
        Just i -> do
            let rel_args@(e:_) = matching_args !! i
                t = typeOf tv_env e
            
            lam_is <- freshIdsN (map (typeOf tv_env) $ fc_args first_fc)
            let branch_on = lam_is !! i
                all_other_is = deleteAt i lam_is
                all_other_vars = map Var all_other_is
            bindee <- freshIdN (idType branch_on)
            
            case unTyApp t of
                TyCon tn _:_
                    | Just (DataTyCon { data_cons = dcs }) <- HM.lookup tn tenv -> do
                        -- Create symbolic functions to continue execution along each alternative branch
                        cont_funcs <- mapM 
                                        (\dc ->
                                                let
                                                    ts = anonArgumentTypes (typeOf tv_env dc)
                                                    sym_f_ty = mkTyFun $ (map idType all_other_is) ++ ts ++ [ret_ty]
                                                in
                                                freshSeededIdN (Name "sym_f" Nothing 0 Nothing) sym_f_ty
                                        ) dcs
                        mapM_ insertSymbolicE cont_funcs
                        
                        -- Set up actual case statement
                        alts <- zipWithM
                                    (\dc f -> do
                                        let ts = anonArgumentTypes (typeOf tv_env dc)
                                        fs <- freshIdsN ts
                                        return $ Alt (DataAlt dc fs) (mkApp $ Var f:all_other_vars ++ map Var fs))
                                    dcs cont_funcs
                        let cse = Case
                                    (Var branch_on)
                                    (bindee)
                                    ret_ty
                                    alts
                            lam_cse = mkLams (zip (repeat TermL) lam_is) cse

                        insertE n lam_cse

                        -- Rewrite constraints
                        let dc_to_cont_funcs = zip (map dc_name dcs) cont_funcs
                            new_fcs = map (\fc ->
                                            let
                                                ith_arg = fc_args fc !! i
                                                Data dc:as = unApp $ inlineVars eenv ith_arg
                                                all_other_args = deleteAt i $ fc_args fc
                                                new_fc = FC { fc_preconds = fc_preconds fc
                                                            , fc_args = all_other_args ++ as
                                                            , fc_ret = fc_ret fc
                                                            }
                                                f_name = case lookup (dc_name dc) dc_to_cont_funcs of
                                                                Just fi -> idName fi
                                                                Nothing -> error "unfoldADTArgs: function not found"
                                            in
                                            (f_name, [new_fc])
                                          )
                                          fcs

                        return new_fcs
                _ -> error "unfoldADTArgs: expected ADT type"
        Nothing -> return [(n, fcs)]

checkDistinct :: (Solver solver, MonadIO m) => solver -> FuncConstraints -> StateNGT t m Bool
checkDistinct solver fcs = do
    kv <- knownValues
    tv_env <- tyVarEnv
    pcs <- getPCStateNG
    pcs' <- foldM (\pcs' (n, fc_list) ->
                    let
                        fc_pcs = zipWith 
                                (\fc i -> 
                                    let
                                        pre = fc_preconds fc
                                        and_pre = foldr (\e1 e2 -> mkApp [Prim And TyUnknown, e1, e2]) (mkTrue kv) pre

                                        prim_args = filter (isPrimType . typeOf tv_env) $ fc_args fc
                                        prim_arg_tys = map (typeOf tv_env) prim_args
                                        call_ty = mkTyFun $ prim_arg_tys ++ [TyLitInt]
                                        uninterp_call =  mkApp $ Var (Id n call_ty):prim_args
                                        implies_func = mkApp [ Prim Implies TyUnknown
                                                             , and_pre
                                                             , mkApp [Prim Eq TyUnknown, uninterp_call, Lit (LitInt i) ]
                                                             ]
                                    in
                                    ExtCond implies_func True
                                    )
                                    fc_list [1..]
                    in
                    return $ foldr PC.insert pcs' fc_pcs
                   ) pcs (HM.toList fcs)
    (s, _) <- SM.get
    r <- liftIO $ check solver s pcs'
    case r of
            SAT _ -> do
                putPCStateNG pcs'
                return True
            _ -> return False

deleteAt :: Int -> [a] -> [a]
deleteAt idx xs = lft ++ rgt
  where (lft, (_:rgt)) = splitAt idx xs

replaceAt :: Int -> a -> [a] -> [a]
replaceAt idx x xs = lft ++ [x] ++ rgt
  where (lft, (_:rgt)) = splitAt idx xs

-- modifyIndex :: Int -> (a -> a) -> [a] -> [a]
-- modifyIndex _ _ [] = error "modifyIndex: unexpected end of list"
-- modifyIndex !0 f (x:xs) = f x:xs
-- modifyIndex !n f (x:xs) = x:modifyIndex (n - 1) f xs

-- Note [Distinguishability]
-- We say two expressions are "distinguishable" if they are (partially) fully reduced,
-- and can be seen to be syntactically different based on the exposed constructors/literals.
-- Two expressions are "indistinguishable" if they are not distinguishable.
-- The "indistinguishable region" of two expressions is the reduced pattern of constructors/literals
-- over which those expressions are indistinguishable.

-- | Returns Just the indistinguishable region of two expressions (looking through variables),
-- or Nothing if the expressions are distinguishable.
--
-- See  Note [Distinguishability].
indistinguishableRegions :: ExprEnv -> Expr -> Expr -> Maybe Expr
indistinguishableRegions eenv e1_ e2_ = go (inlineVars eenv e1_) (inlineVars eenv e2_)
    where      
        -- (Possibly) indistinguishable matching
        go (App e1 e2) (App e1' e2') = liftM2 App (go e1 e1') (go e2 e2')
        go dc@(Data (DataCon { dc_name = n1 })) (Data (DataCon { dc_name = n2 })) | n1 == n2 = Just dc
                                                                                  | otherwise = Nothing
        go t@(Type t1) (Type t2) | t1 == t2 = Just t
                                 | otherwise = Nothing
        go l@(Lit l1) (Lit l2) | l1 == l2 = Just l
                               | otherwise = Nothing

        -- Distinguishable, so return Nothing
        go (Data _) e@(App _ _) | Data _:_ <- unApp e = Nothing
        go e@(App _ _) (Data _) | Data _:_ <- unApp e = Nothing
        go (Data _) (Type _) = Nothing
        go (Type _) (Data _) = Nothing

        go _ _ = Just $ Prim Undefined TyBottom

        -- go a@(App _ _) _ | Data _:_ <- unApp a