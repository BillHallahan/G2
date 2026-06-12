{-# LANGUAGE BangPatterns, MultiWayIf, OverloadedStrings #-}

module G2.Execution.FuncConstraints where

import G2.Config
import G2.Execution.NormalForms
import G2.Execution.PrimitiveEval
import G2.Execution.Reducer
import G2.Language as L
import qualified G2.Language.ExprEnv as E
import G2.Language.Monad
import qualified G2.Language.PathConds as PC
import qualified G2.Language.Stack as Stck
import G2.Lib.Printers
import G2.Solver

import Control.Exception
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
                    , fc_ret = Var ret_id
                    
                    , fc_split_on = fmap (const NoSplit) es }
            
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

addFCArgs :: [Expr] -> FuncConstraint -> FuncConstraint
addFCArgs new_args fc = fc { fc_args = fc_args fc ++ new_args
                           , fc_split_on = fc_split_on fc ++ map (const NoSplit) new_args}

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
                    -- liftIO . putStrLn $ case r of Just _ -> "Just"; Nothing -> "Nothing"
                    case r of
                        Just (s', ng') -> return (Finished, [(s', ())], b { name_gen = ng' })
                        Nothing -> do
                            -- Function constraints were not solved
                            ((is, fc'), (s', !ng')) <- runStateNGT (do
                                let fcs = sym_func_constraints s
                                -- Add extra calls to higher order functions
                                added_higher_fcs <- mapM (uncurry addHigherOrderCalls) $ HM.toList fcs
                                let fc_higher_reassembled = HM.fromList added_higher_fcs

                                -- Gather unreduced expressions in the function constraints, and set up state to reduce them
                                fc_wrapper <- addWrappersToFC fc_higher_reassembled
                                non_red_v <- collectNonReducedVars fc_wrapper
                                return (non_red_v, fc_wrapper)
                                ) s (name_gen b)

                            case is of
                                [] -> return (Finished, [], b)
                                (head_i:tail_is) ->
                                    let
                                        ce = curr_expr s'
                                        stck = foldl' (\st i -> Stck.push (CurrExprFrame NoAction (CurrExpr Evaluate $ Var i)) st)
                                                      (Stck.push (CurrExprFrame NoAction ce) Stck.empty )
                                                      tail_is
                                        s'' = s' { curr_expr = CurrExpr Evaluate (Var head_i)
                                                 , exec_stack = stck
                                                 , sym_func_constraints = fc'
                                                 , solving_sym_func_constraints = SolvingFCs }
                                    in
                                    return (Finished, [(s'', ())], b { name_gen = ng' }) -- TODO
                 | otherwise = return (Finished, [], b)

------------------------------------------------------------------------------
-- Collecting expressions to reduce when solving fails
------------------------------------------------------------------------------

-- | Expands function definitions to include extra calls to higher order functions.
addHigherOrderCalls :: MonadIO m => Name -> [FuncConstraint] -> StateNGT t m (Name, [FuncConstraint])
addHigherOrderCalls n [] = return (n, [])
addHigherOrderCalls n fcs@(first_fc:_) = do
    tv_env <- tyVarEnv
    let arg_ts = map (typeOf tv_env) $ fc_args first_fc
        (func_inds, higher_tys) = unzip . filter (isTyFun . snd) $ zip [0..] arg_ts
    
    case func_inds of
        [] -> return (n, fcs)
        (_:_) -> do
            let ret_ty = typeOf tv_env $ fc_ret first_fc
                higher_ret_ty = map returnType higher_tys
                t_new = mkTyFun $ arg_ts ++ higher_ret_ty ++ [ret_ty]

            -- Update definition of original symbolic function.
            f_new <- freshSeededIdN (Name "f_h" Nothing 0 Nothing) t_new
            insertSymbolicE f_new

            lam_is <- freshIdsN (map (typeOf tv_env) $ fc_args first_fc)
            higher_args_apps <- mapM (\j -> do
                let i = lam_is !! j
                    ts = anonArgumentTypes $ typeOf tv_env i
                as <- freshIdsN ts
                mapM_ insertSymbolicE as
                return (as, mkApp $ Var i:map Var as)) func_inds
            let (higher_args, higher_apps) = unzip higher_args_apps

            let e = mkLams (zip (repeat TermL) lam_is)
                  . mkApp
                  $ Var f_new:map Var lam_is ++ higher_apps
            
            insertE n e

            -- Update function constraints
            let fcs' = map (\fc@(FC { fc_args = as }) ->
                        let
                            new_as = zipWith
                                        (\f f_as -> mkApp $ f:map Var f_as)
                                        (map (as !!) func_inds)
                                        higher_args
                        in
                        fc { fc_args = as ++ new_as
                           , fc_split_on = fc_split_on fc ++ map (const NoSplit) new_as }
                        ) fcs

            return (idName f_new, fcs')

-- | Get expressions that have not been fully reduced. 
collectNonReducedVars :: Monad m => FuncConstraints -> StateNGT t m [Id]
collectNonReducedVars fcs = do
    eenv <- exprEnv

    let collect seen (Var i@(Id n _))
            | n `notElem` seen
            , Just e <- E.lookup n eenv
            , isExprValueForm eenv e = collect (HS.insert n seen) e
            | E.isSymbolic n eenv = []
            | otherwise = [i]
        collect seen e
            | Data _:es <- unApp e = concatMap (collect seen) es
        collect _ _ = []
    
    return . concatMap (
                    concatMap (concatMap (collect HS.empty) . fc_args)
             )
           $ HM.elems fcs

addWrappersToFC :: Monad m => FuncConstraints -> StateNGT t m FuncConstraints
addWrappersToFC =
    mapM (
            mapM (\fc -> do
                as' <- SM.evalStateT (mapM addVarWrappers $ fc_args fc) HS.empty
                return $ fc { fc_args = as' }
            )
         )

-- Replace any non-WHNF expression with a variable that points to that non-WHNF epxression.
addVarWrappers :: Monad m => Expr -> SM.StateT (HS.HashSet Name) (SM.StateT (State t, NameGen) m) Expr
addVarWrappers e
    | d@(Data _):es <- unApp e = do
        es' <- mapM addVarWrappers es
        return . mkApp $ d:es'
addVarWrappers v@(Var (Id n _)) = do
    seen <- SM.get
    eenv <- SM.lift $ exprEnv
    case E.lookup n eenv of
        Just e | n `notElem` seen -> do
            SM.put $ HS.insert n seen
            addVarWrappers e
            return v
        _ -> return v
addVarWrappers e = do
    eenv <- SM.lift $ exprEnv
    case isExprValueForm eenv e of
        True -> return e
        False -> do
            tv_env <- SM.lift $ tyVarEnv
            i <- SM.lift $ freshIdN (typeOf tv_env e)
            SM.lift $ insertE (idName i) e
            return (Var i)

limitSolvingFuncConstraintPieces :: Monad m => Reducer m Int t
limitSolvingFuncConstraintPieces = mkSimpleReducer (\_ -> 200) go
    where
        go 0 s b | solving_sym_func_constraints s == SolvingFCs =
            let
                (e, eenv, stck) = collapseStack (exec_stack s) (expr_env s) (getExpr s)
                s' = s { curr_expr = CurrExpr Return e
                       , expr_env = eenv
                       , exec_stack = stck }
            in
            return (Finished, [(s', 200)], b)
        go !c s b 
            | solving_sym_func_constraints s == SolvingFCs
            , Stck.null (exec_stack s)
            , CurrExpr Return _ <- curr_expr s = return (Finished, [(s, 200)], b)
            | solving_sym_func_constraints s == SolvingFCs = return (InProgress, [(s, c - 1)], b)
        go _ s b = return (NoProgress, [(s, 200)], b)

collapseStack :: Stck.Stack Frame -> ExprEnv -> Expr -> (Expr, ExprEnv, Stck.Stack Frame)
collapseStack stck eenv e
    | Just (CaseFrame i t as, stck') <- fr = collapseStack stck' eenv (Case e i t as)
    | Just (ApplyFrame e', stck') <- fr = collapseStack stck' eenv (App e e')
    | Just (UpdateFrame n, stck') <- fr = collapseStack stck' (E.insert n e eenv) e
    | Just (CastFrame coer, stck') <- fr = collapseStack stck' eenv (Cast e coer)
    | Just (CatchFrame catch, stck') <- fr = collapseStack stck' eenv (mkApp [Prim Catch TyUnknown, e, catch])
    | Just (AssumeFrame assume_e, stck') <- fr = collapseStack stck' eenv (Assume Nothing assume_e e)
    | Just (AssertFrame fc assume_e, stck') <- fr = collapseStack stck' eenv (L.Assert fc assume_e e)
    | Just (CurrExprFrame _ _, _) <- fr = (e, eenv, stck)
    | Just (LitTableFrame _ _, _) <- fr = error "collapseStack: LitTableFrame not supported"
    | Nothing <- fr = (e, eenv, stck)
    where
        fr = Stck.pop stck

------------------------------------------------------------------------------
-- Solving Function Constraints
------------------------------------------------------------------------------

data FCRes = SatFC FuncConstraints | UnsatFC deriving Eq

data FCProgress = MadeProgressFC | NoProgressFC deriving (Eq, Show)

type FCState t m a = SM.StateT (State t, NameGen) (SM.StateT FCProgress m) a

getProgress :: Monad m => FCState t m FCProgress
getProgress = SM.lift SM.get

resetProgress :: Monad m => FCState t m ()
resetProgress = SM.lift $ SM.put NoProgressFC

madeProgress :: Monad m => FCState t m ()
madeProgress = SM.lift $ SM.put MadeProgressFC

solveFuncConstraints :: (Solver solver, MonadIO m) => solver -> State t -> NameGen -> m (Maybe (State t, NameGen))
solveFuncConstraints solver s@(State { sym_func_constraints = fc }) ng = do
    -- liftIO $ do
    --     putStrLn "------------------------"
    --     putStrLn "About to call solve FC"
    --     putStrLn "------------------------"
    (r, (s', !ng')) <- SM.evalStateT (runStateNGT (solveFC solver (-1) fc) s ng) NoProgressFC
    return $ case r of
                    SatFC fcs' -> Just (s' { solving_sym_func_constraints = SolvedFCs
                                           , sym_func_constraints = fcs' }, ng')
                    _ -> Nothing


-- TODO: Do we actually need the counter here?
solveFC :: (Solver solver, MonadIO m) => solver -> Int -> FuncConstraints -> FCState t m FCRes
solveFC _ 0 _ = return UnsatFC
solveFC solver !n fcs = do
    -- Convert functions with only a single constraint into constants
    -- fcs_nosingle <- return . HM.mapMaybe id =<< HM.traverseWithKey solveSingleton fcs
    let pg = mkPrettyGuide (HM.toList fcs)
    -- eenv_init <- exprEnv
    -- liftIO $ putStrLn $ "fcs =\n" ++ T.unpack (prettyFuncConstraints pg $ inlineVars eenv_init fcs)  

    distinct <- checkDistinct solver fcs

    case distinct of
        True -> return (SatFC fcs)
        False -> do
            resetProgress

            fcs_simp_pieces <- concatMapM (uncurry simplifyReturns) $ HM.toList fcs
            let fc_simp_reassembled = HM.fromListWith (++) fcs_simp_pieces

            let pg_rets = updatePrettyGuide (HM.toList fc_simp_reassembled) pg
            -- liftIO $ putStrLn $ "fc_simp_returns =\n" ++ T.unpack (prettyFuncConstraints pg_rets fc_simp_reassembled)  

            -- Replace ADT symbolic variables with case expressions
            fcs_replaced_sym_adt <- mapM replaceADTSymVars fc_simp_reassembled

            fcs_precond <- mapM caseToPreCond fcs_replaced_sym_adt
            let pg_precond = updatePrettyGuide (HM.toList fcs_precond) pg
            -- eenv <- exprEnv
            -- liftIO $ putStrLn $ "fcs_precond =\n" ++ T.unpack (prettyFuncConstraints pg_precond $ inlineVars eenv fcs_precond)  

            -- Introduce branches on ADTs
            fcs_unfold_adt_pieces <- concatMapM (uncurry unfoldADTArgs) $ HM.toList fcs_precond
            let fc_unfold_adt_reassembled = HM.fromListWith (++) fcs_unfold_adt_pieces

            -- liftIO $ putStrLn "after unfoldADTArgs"
            let pg_assem = updatePrettyGuide (HM.toList fc_unfold_adt_reassembled) pg_precond
            -- eenv_asem <- exprEnv
            -- liftIO $ putStrLn $ "fc_unfold_adt =\n" ++ T.unpack (prettyFuncConstraints pg_assem $ inlineVars eenv_asem fc_unfold_adt_reassembled)

            -- Branch on literals, with the aim of splitting up ADTs that are in WHNF from those that are not
            split_whnf_pieces <- concatMapM (uncurry splitWHNFAndNonWHNF) $ HM.toList fc_unfold_adt_reassembled
            let fc_unfold_split_whnf_reassembled = HM.fromListWith (++) split_whnf_pieces

            -- liftIO $ putStrLn "after splitWHNFAndNonWHNF"
            let pg_whnf_assem = updatePrettyGuide (HM.toList fc_unfold_split_whnf_reassembled) pg_assem
            -- eenv_whnf_assem <- exprEnv
            -- liftIO $ putStrLn $ "fc_unfold_split_whnf_reassembled =\n" ++ T.unpack (prettyFuncConstraints pg_whnf_assem $ inlineVars eenv_whnf_assem fc_unfold_split_whnf_reassembled)

            prog <- getProgress
            -- liftIO . putStrLn $ "end prog = " ++ show prog

            case prog of
                MadeProgressFC -> solveFC solver (n - 1) fc_unfold_split_whnf_reassembled
                NoProgressFC -> return UnsatFC

solveSingleton :: Monad m => Name -> [FuncConstraint] -> FCState t m (Maybe [FuncConstraint])
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
simplifyReturns :: MonadIO m => Name -> [FuncConstraint] -> FCState t m [(Name, [FuncConstraint])]
simplifyReturns n fcs = do
    eenv <- exprEnv
    tv_env <- tyVarEnv

    case fcs of
        (fc:_) | -- Check if all return values have the same constructor
                 let r = fc_ret fc
                     rs = map fc_ret fcs
               , Data dc@(DataCon { dc_name = dc_n, dc_type = dc_ty }):dc_args <- unApp $ inlineVars eenv r
               , all (sameConstructor eenv dc_n) rs -> do
                    -- Set up the original function to return the required data constructor
                    -- with arguments constructed by fresh symbolic functions 
                    let existing_args = map (typeOf tv_env) $ fc_args fc

                    lam_is <- freshIdsN existing_args
                    let _:tycon_ts = unTyApp $ typeOf tv_env r
                        named_ts = tyForAllBindings dc_ty
                        ty_map = HM.fromList $ zipWith (\i t -> (idName i, t)) named_ts tycon_ts
                        anon_ts = replaceTyVars ty_map $ anonArgumentTypes dc_ty

                    per_arg_func <- mapM (\t -> do
                                            fn <- freshSeededStringN "sym_f"
                                            let fi = Id fn (mkTyFun $ existing_args ++ [t])
                                            insertSymbolicE fi
                                            return fi
                                         ) anon_ts

                    let ret_val = mkApp $ Data dc:map Type tycon_ts ++ map (\f -> (mkApp $ (Var f):map Var lam_is)) per_arg_func
                        func_def = mkLams (zip (repeat TermL) lam_is) ret_val
                    insertE n func_def

                    -- Convert existing function constraints into constraints for the newly created functions
                    let new_fcs = concatMap (\this_fc -> 
                                    case filter (not . isType) . unApp . inlineVars eenv $ fc_ret this_fc of
                                        [] -> error "simplifyReturns: impossible"
                                        (_:ret_p) -> zipWith (\f p -> (idName f, [this_fc { fc_ret = p }])) per_arg_func ret_p
                                    ) fcs

                    madeProgress
                    return new_fcs

        _ -> return [(n, fcs)]
    where
        isType (Type _) = True
        isType _ = False

        sameConstructor eenv dc_n e
                | Data (DataCon { dc_name = dc_n', dc_type = dc_ty }):_ <- unApp $ inlineVars eenv e
                , dc_n == dc_n' = True
                | otherwise = False

-- | Replace symbolic variables with ADT types with a case statement on a symbolic int, where
-- each branch returns a different constructor of that ADT, with symbolic arguments.
replaceADTSymVars :: MonadIO m => [FuncConstraint] -> FCState t m [FuncConstraint]
replaceADTSymVars fcs = do
    eenv <- exprEnv
    tenv <- typeEnv
    tv_env <- tyVarEnv

    mapM (\fc -> do 
        mapM_ (go eenv tenv tv_env) (fc_args fc)
        go eenv tenv tv_env $ fc_ret fc
        return $ fc) fcs
    where
        go eenv tenv tv_env e
            | Var (Id n t) <- inlineVars eenv e
            , E.isSymbolic n eenv
            , TyCon tn _:tycon_ts <- unTyApp $ tyVarSubst tv_env t
            , Just (DataTyCon { data_cons = dcs }) <- HM.lookup tn tenv = do
                branch_n <- freshSeededStringN "n"
                bindee <- freshSeededStringN "bindee"
                let branch_i = Id branch_n TyLitInt
                    branch_var = Var branch_i
                insertSymbolicE branch_i
                insertPCStateNG (ExtCond (mkApp $ [Prim Le TyUnknown, Lit (LitInt 1), Var branch_i]) True)
                insertPCStateNG (ExtCond (mkApp $ [Prim Le TyUnknown, Var branch_i, Lit (LitInt $ genericLength dcs)]) True)

                alts_expr <- mapM (\dc -> do
                                    let dc_ty = typeOf tv_env dc
                                        named_ts = tyForAllBindings dc_ty
                                        ty_map = HM.fromList $ zipWith (\i t -> (idName i, t)) named_ts tycon_ts
                                        anon_ts = replaceTyVars ty_map $ anonArgumentTypes dc_ty

                                    dc_as <- freshIdsN anon_ts
                                    mapM insertSymbolicE dc_as
                                    return . mkApp $ Data dc:map Type tycon_ts ++ map Var dc_as
                            ) dcs
                
                liftIO . putStrLn $ "alts_expr = " ++ show alts_expr
                let alts = zipWith Alt (map (LitAlt . LitInt) [1..]) alts_expr
                    cse = Case
                            branch_var
                            (Id bindee TyLitInt)
                            t
                            alts
                insertE n cse

                madeProgress
                return ()

            | otherwise = do
                return ()

caseToPreCond :: MonadIO m => [FuncConstraint] -> FCState t m [FuncConstraint]
caseToPreCond fcs = concatMapM goArg fcs >>= concatMapM goRet
    where
        goArg fc@(FC { fc_preconds = pre, fc_args = es }) = do
            eenv <- exprEnv
            let es' = map (getOutCases eenv) es
                case_pats = map getCasePats es'
                m_ind_case_pat = findIndex isJust case_pats
            case m_ind_case_pat of
                Just ind -> do
                    let Just (branch_i, alts) = case_pats !! ind
                        eq i = mkApp $ [Prim Eq TyUnknown, Var branch_i, Lit i]
                    
                    let fc_branch = map (\(lit_v, dc) -> fc { fc_preconds = eq lit_v:pre, fc_args = replaceAt ind dc es'}) alts

                    madeProgress
                    return fc_branch
                Nothing -> return [fc]
        
        goRet fc@(FC { fc_preconds = pre, fc_ret = e }) = do
            eenv <- exprEnv
            let e' = getOutCases eenv e
                m_case_pat = getCasePats e'
            case m_case_pat of
                Just (branch_i, alts) -> do
                    let eq i = mkApp $ [Prim Eq TyUnknown, Var branch_i, Lit i]
                    let fc_branch = map (\(lit_v, dc) -> fc { fc_preconds = eq lit_v:pre, fc_ret = dc}) alts

                    madeProgress
                    return fc_branch
                Nothing -> return [fc]
                    
        getOutCases eenv v@(Var (Id n _)) =
            let e = inlineVars eenv v in
            case e of
                cse@(Case _ _ _ (Alt (LitAlt _) _:_)) -> cse
                _ -> v
        getOutCases _ e = e

        getCasePats (Case (Var i) (Id _ TyLitInt) _ alts) = Just (i, map (\(Alt (LitAlt l) dc) -> (l, dc)) alts)
        getCasePats _ = Nothing

-- | Find an argument which is an ADT and in WHNF in all function constraints, and use that
-- argument to do a case split.
unfoldADTArgs :: MonadIO m => Name -> [FuncConstraint] -> FCState t m [(Name, [FuncConstraint])]
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
                                                all_other_split_ons = deleteAt i $ fc_split_on fc
                                                new_fc = FC { fc_preconds = fc_preconds fc
                                                            , fc_args = all_other_args ++ as
                                                            , fc_split_on = all_other_split_ons ++ map (const NoSplit) as
                                                            , fc_ret = fc_ret fc
                                                            }
                                                f_name = case lookup (dc_name dc) dc_to_cont_funcs of
                                                                Just fi -> idName fi
                                                                Nothing -> error "unfoldADTArgs: function not found"
                                            in
                                            (f_name, [new_fc])
                                          )
                                          fcs

                        madeProgress
                        return new_fcs
                _ -> error "unfoldADTArgs: expected ADT type"
        Nothing -> return [(n, fcs)]

-- | Find an argument that is in WHNF for some function constraints, and not in WHNF for other function constraints,
-- and use the literal values in the constraints to split up these cases into two constraints for two separate functions,
-- one for the WHNF arguments, and one for the non-WHNF arguments.
splitWHNFAndNonWHNF :: MonadIO m => Name -> [FuncConstraint] -> FCState t m [(Name, [FuncConstraint])]
splitWHNFAndNonWHNF n [] = return []
splitWHNFAndNonWHNF n fcs@(first_fc:_) = do
    eenv <- exprEnv
    tv_env <- tyVarEnv

    let matching_args = transpose $ map fc_args fcs
        only_some_whnf = findIndices (\e -> any (isADT . inlineVars eenv) e
                                        && any (not . isADT . inlineVars eenv) e ) matching_args
    
    let arg_tys = map (typeOf tv_env) $ fc_args first_fc

    case any isPrimType arg_tys of
        True -> splitWHNFAndNonWHNFIndices only_some_whnf [(n, fcs)]
        False -> return [(n, fcs)]

splitWHNFAndNonWHNFIndices :: MonadIO m => [Int] -> [(Name, [FuncConstraint])] -> FCState t m [(Name, [FuncConstraint])]
splitWHNFAndNonWHNFIndices [] n_fcs = return n_fcs
splitWHNFAndNonWHNFIndices (i:is) n_fcs = do
    n_fcs' <- concatMapM (uncurry (splitWHNFAndNonWHNFIndex i)) n_fcs
    splitWHNFAndNonWHNFIndices is n_fcs'

splitWHNFAndNonWHNFIndex :: MonadIO m =>
                            Int -- ^ Index to split on
                         -> Name
                         -> [FuncConstraint]
                         -> FCState t m [(Name, [FuncConstraint])]
splitWHNFAndNonWHNFIndex _ n [] = return []
splitWHNFAndNonWHNFIndex i n fcs@(first_fc:_) | fc_split_on first_fc !! i == Split  = return [(n, fcs)]
splitWHNFAndNonWHNFIndex i n fcs@(first_fc:_) = do
    eenv <- exprEnv
    tenv <- typeEnv
    tv_env <- tyVarEnv
    
    let arg_tys = map (typeOf tv_env) $ fc_args first_fc
        ret_ty = typeOf tv_env $ fc_ret first_fc

    lam_is <- freshIdsN (map (typeOf tv_env) $ fc_args first_fc)
    let prim_ty_is = filter (isPrimType . idType) lam_is

    ty_bool <- tyBoolT
    dc_true <- mkDCTrueM
    dc_false <- mkDCFalseM

    pred <- freshSeededIdN (Name "pred" Nothing 0 Nothing) . mkTyFun $ map idType prim_ty_is ++ [ty_bool]
    f_true <- freshSeededIdN (Name "f_true" Nothing 0 Nothing) . mkTyFun $ arg_tys ++ [ret_ty]
    f_false <- freshSeededIdN (Name "f_false" Nothing 0 Nothing) . mkTyFun $ arg_tys ++ [ret_ty]

    bindee <- freshIdN ty_bool
    let pred_app = mkApp $ Var pred:map Var prim_ty_is
        f_true_app = mkApp $ Var f_true:map Var lam_is
        f_false_app = mkApp $ Var f_false:map Var lam_is
        cse = Case pred_app bindee ret_ty
                        [ Alt (DataAlt dc_true []) f_true_app
                        , Alt (DataAlt dc_false []) f_false_app ]
        lam_cse = mkLams (zip (repeat TermL) lam_is) cse

    insertE n lam_cse

    -- Rewrite constraints which do not have argument in WHNF
    non_whnf_cons <- mapMaybeM
                        (\fc -> if | not . isADT . inlineVars eenv $ fc_args fc !! i -> do
                                        -- Add a path constraint that the predicate does not hold
                                        let pred_args = filter (isPrimType . typeOf tv_env) $ fc_args fc
                                            pred_app = mkApp $ Var pred:pred_args
                                        insertPCStateNG $ ExtCond pred_app False
                                        let fc_non_whnf = fc { fc_preconds = App (Prim Not TyUnknown) (pred_app):fc_preconds fc
                                                             , fc_split_on = replaceAt i Split $ fc_split_on fc}
                                        return $ Just (idName f_false, [fc_non_whnf])
                                    | otherwise -> return Nothing
                        )
                        fcs

    -- Rewrite constraints which do have argument in WHNF.
    -- Allow either satisfying OR not satisfying the predicate
    whnf_cons <- concatMapM (\fc -> if | isADT . inlineVars eenv $ fc_args fc !! i -> do
                                        -- Add a path constraint that the predicate does not hold
                                        let pred_args = filter (isPrimType . typeOf tv_env) $ fc_args fc
                                            pred_app = mkApp $ Var pred:pred_args
                                            fc_true = FC { fc_preconds = pred_app:fc_preconds fc
                                                            , fc_args = fc_args fc
                                                            , fc_split_on = replaceAt i Split $ fc_split_on fc
                                                            , fc_ret = fc_ret fc
                                                            }
                                            fc_false = FC { fc_preconds = App (Prim Not TyUnknown) (pred_app):fc_preconds fc
                                                            , fc_args = fc_args fc
                                                            , fc_split_on = replaceAt i Split $ fc_split_on fc
                                                            , fc_ret = fc_ret fc
                                                            }

                                        return [(idName f_true, [fc_true]), (idName f_false, [fc_false])]
                                        | otherwise -> return []
                        )
                        fcs

    madeProgress
    return $ non_whnf_cons ++ whnf_cons

-- | Checks if we can find solutions to all functions.
-- Uses an SMT solver and the theory of uninterpreted functions to solve for literal inputs/outputs.
checkDistinct :: (Solver solver, MonadIO m) => solver -> FuncConstraints -> FCState t m Bool
checkDistinct solver fcs = do
    -- We optimistically insert into the ExprEnv throughout this code,
    -- and revert to the old ExprEnv at the end if we fail to find a solution.
    eenv <- exprEnv
    tv_env <- tyVarEnv
    kv <- knownValues
    pcs <- getPCStateNG

    fcs_split <- splitReturns fcs

    -- let pg = mkPrettyGuide (HM.toList fcs_split)
    -- eenv <- exprEnv
    -- liftIO $ putStrLn $ "fcs_split =\n" ++ T.unpack (prettyFuncConstraints pg $ inlineVars eenv fcs_split)  

    pcs' <- foldM (\pcs' (n, fc_list) ->
        case fc_list of
            [] -> return pcs'
            (fc_first:_) -> do
                    let prim_arg_tys = map (typeOf tv_env) $ filter (isPrimType . typeOf tv_env) $ fc_args fc_first
                        call_ty = mkTyFun $ prim_arg_tys ++ [TyLitInt]
                    sel_func <- freshSeededIdN (Name "sel" Nothing 0 Nothing) call_ty

                    let fc_prim = map (\fc -> fc { fc_args = filter (isPrimType . typeOf tv_env) $ fc_args fc}) fc_list
                    (unified_id, fc_unified) <- unifyAllRetSymVars fc_prim
                    -- Filter to only constraints that do not return symbolic variables.
                    -- Constraints returning symbolic variables may return any value; thus they may be ignored.
                    fc_no_sym_ret <- filterM (\fc -> case fc_ret fc of
                                                        (Var (Id n t)) -> do
                                                            m_conc_or_sym <- deepLookupConcOrSymE n
                                                            case m_conc_or_sym of
                                                                Just (E.Sym _) -> return $ isPrimType t
                                                                _ -> return True
                                                        _ -> return True) fc_unified

                    let fc_pcs = zipWith 
                                (\i fc -> 
                                    let
                                        pre = fc_preconds fc
                                        and_pre = foldr (\e1 e2 -> mkApp [Prim And TyUnknown, e1, e2]) (mkTrue kv) pre

                                        prim_args = filter (isPrimType . typeOf tv_env) $ fc_args fc
                                        uninterp_call =  mkApp $ Var sel_func:prim_args

                                        -- Note [Uninterpreted Return Value] 
                                        -- If we are returning an ADT, returning an Int that can then be mapped to that ADT.
                                        -- If we are returning a primitive type, just return it directly.
                                        uninterp_ret = if isPrimType (typeOf tv_env $ fc_ret fc)
                                                                then fc_ret fc
                                                                else Lit (LitInt i)

                                        implies_func = mkApp [ Prim Implies TyUnknown
                                                             , and_pre
                                                             , mkApp [Prim Eq TyUnknown, uninterp_call, uninterp_ret ]
                                                             ]
                                    in
                                    ExtCond implies_func True
                                    )
                                    [1..] fc_no_sym_ret
                    
                    -- We optimistically insert expressions into the ExprEnv; if we do not find a solution,
                    -- we revert to the old ExprEnv
                    insertSymbolicE sel_func

                    lam_is <- freshIdsN (map (typeOf tv_env) $ fc_args fc_first)
                    let prim_lam_is = filter (isPrimType . typeOf tv_env) lam_is
                        sel_func_app = mkApp . map Var $ sel_func:prim_lam_is

                    -- See Note [Uninterpreted Return Value], above
                    if isPrimType (typeOf tv_env $ fc_ret fc_first)
                        then
                            insertE n $ mkLams (zip (repeat TermL) lam_is) sel_func_app
                        else do
                            bindee <- freshIdN TyLitInt
                            let def_alt = Alt Default (Var unified_id)
                                alts = zipWith (\i fc -> Alt (LitAlt (LitInt i)) $ fc_ret fc) [1..] fc_no_sym_ret 
                                ret_ty = typeOf tv_env (fc_ret fc_first)
                                cse = Case sel_func_app bindee ret_ty (alts ++ [def_alt])
                                lam_cse = mkLams (zip (repeat TermL) lam_is) cse
                            insertE n lam_cse
                    
                    return $ foldr PC.insert pcs' fc_pcs
            ) pcs (HM.toList fcs_split)
    (s, _) <- SM.get
    r <- liftIO $ check solver s pcs'
    case r of
            SAT _ -> do
                putPCStateNG pcs'
                return True
            _ -> do
                -- We did not find a solution, revert to old ExprEnv
                putExprEnv eenv
                return False    

-- | Adjust all symbolic variables of ADT types being returned from function constraints
-- to be the same (fresh) symbolic value.
-- This then allows us to ignore these constraints.
unifyAllRetSymVars :: Monad m => [FuncConstraint] -> FCState t m (Id, [FuncConstraint])
unifyAllRetSymVars [] = do
    unify_id <- freshSeededIdN (Name "unify" Nothing 0 Nothing) TyUnknown
    return (unify_id, [])
unifyAllRetSymVars fcs@(fc_first:_) = do
    eenv <- exprEnv
    tv_env <- tyVarEnv

    let ret_ty = typeOf tv_env $ fc_ret fc_first
    unify_id <- freshSeededIdN (Name "unify" Nothing 0 Nothing) ret_ty
    insertSymbolicE unify_id
    if | not (isPrimType ret_ty) -> do
            fcs' <- mapM (\fc -> case fc_ret fc of
                                    (Var (Id n _))
                                        | Just (E.Sym (Id sym_n _)) <- E.deepLookupConcOrSym n eenv -> do
                                            insertE sym_n (Var unify_id)
                                            return fc { fc_ret = Var unify_id }
                                        | otherwise -> return fc
                                    _ -> return fc) fcs
            return (unify_id, fcs')
       | otherwise -> return (unify_id, fcs)

-- If the same function is returning different constructors for an ADT, try to split it up using literals
splitReturns :: MonadIO m => FuncConstraints -> FCState t m FuncConstraints
splitReturns fcs = do
    resetProgress
    split <- concatMapM (uncurry splitReturns') $ HM.toList fcs
    let fcs' = HM.fromListWith (++) split

    prog <- getProgress
    case prog of
        MadeProgressFC -> splitReturns fcs'
        NoProgressFC -> return fcs'

splitReturns' :: MonadIO m => Name -> [FuncConstraint] -> FCState t m [(Name, [FuncConstraint])]
splitReturns' n [] = return []
splitReturns' n fcs@(first_fc:_) = do
    eenv <- exprEnv
    tenv <- typeEnv
    tv_env <- tyVarEnv

    if | let ret_ty = unTyApp . tyVarSubst tv_env . typeOf tv_env $ fc_ret first_fc
       , TyCon tn _:tycon_ts <- ret_ty
       , Just (DataTyCon { data_cons = dcs}) <- HM.lookup tn tenv
       , all (isADT . inlineVars eenv . fc_ret) fcs -> do

            let arg_tys = map (typeOf tv_env) $ fc_args first_fc
                ret_ty = typeOf tv_env $ fc_ret first_fc

            lam_is <- freshIdsN (map (typeOf tv_env) $ fc_args first_fc)
            let prim_ty_is = filter (isPrimType . idType) lam_is

            -- Creating new function definition
            sel <- freshSeededIdN (Name "sel" Nothing 0 Nothing) . mkTyFun $ map idType prim_ty_is ++ [TyLitInt]
            insertSymbolicE sel

            bindee <- freshIdN ret_ty

            dc_funcs <- foldM (\hm dc@(DataCon { dc_name = dc_n, dc_type = dc_ty}) -> do
                                let named_ts = tyForAllBindings dc_ty
                                    ty_map = HM.fromList $ zipWith (\i t -> (idName i, t)) named_ts tycon_ts
                                fs <- mapM
                                    (\arg_t -> freshSeededIdN
                                                    (Name "dc_branch" Nothing 0 Nothing) (mkTyFun $ map idType prim_ty_is ++ [arg_t]))
                                                    (replaceTyVars ty_map $ anonArgumentTypes dc_ty)
                                mapM_ insertSymbolicE fs
                                return $ HM.insert dc_n fs hm
                             ) HM.empty dcs

            alts <- zipWithM (\i dc -> do
                        let Just fs = HM.lookup (dc_name dc) dc_funcs
                            fs_apps = map (\f -> mkApp $ Var f:map Var prim_ty_is) fs
                            alt_e = mkApp $ Data dc:map Type tycon_ts ++ fs_apps
                        return $ Alt (LitAlt (LitInt i)) alt_e) [0..] dcs
            let sel_app = mkApp $ Var sel:map Var prim_ty_is
                cse = Case sel_app bindee ret_ty alts
                lam_cse = mkLams (zip (repeat TermL) lam_is) cse

            insertE n lam_cse

            -- Adjusting constraints
            let fcs_sel = map (\fc ->
                                    case unApp . inlineVars eenv $ fc_ret fc of
                                        Data dc:_ ->
                                            fc { fc_args = filter (isPrimType . typeOf tv_env) $ fc_args fc
                                               , fc_ret = Lit $ LitInt (toInteger . fromJust $ elemIndex (dc_name dc) $ map dc_name dcs) }
                              ) fcs
                fcs_branches = concatMap (\fc ->
                                    case unApp . inlineVars eenv $ fc_ret fc of
                                        Data dc:es
                                            | Just fs <- HM.lookup (dc_name dc) dc_funcs ->
                                                zipWith (\f r_e -> 
                                                        let
                                                            fc' = fc { fc_args = filter (isPrimType . typeOf tv_env) $ fc_args fc
                                                                     , fc_ret = r_e}
                                                        in
                                                        (idName f, [fc'])
                                                    ) fs (filter (not . isType . inlineVars eenv) es)
                                        _ -> error $ "splitReturns: impossible expr" ++ show (inlineVars eenv $ fc_ret fc)) fcs

            madeProgress
            return $ (idName sel, fcs_sel):fcs_branches
       | otherwise -> return [(n, fcs)]
       where
        isType (Type _) = True
        isType _ = False

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