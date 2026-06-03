{-# LANGUAGE BangPatterns, OverloadedStrings #-}

module G2.Execution.FuncConstraints where

import G2.Config
import G2.Execution.Reducer
import G2.Language
import qualified G2.Language.ExprEnv as E
import G2.Language.Monad
import qualified G2.Language.Stack as Stck

import Control.Monad
import Control.Monad.Extra
import Control.Monad.IO.Class
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import Data.List

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
addFC n fc [] = [FR n [fc]]
addFC n fc (fr@(FR { func_name = fr_n, func_constraints = cons } ):xs)
    | n == fr_n = fr { func_constraints = fc:cons }:xs
    | otherwise = fr:addFC n fc xs

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

solveFuncConstraintsReducer :: MonadIO m => Reducer m () t
solveFuncConstraintsReducer = mkSimpleReducer (\_ -> ()) go
    where
        go _ s b | true_assert s = do
                    r <- solveFuncConstraints s (name_gen b)
                    liftIO . putStrLn $ case r of Just _ -> "Just"; Nothing -> "Nothing"
                    error "solveFuncConstraintsReducer"
                 | otherwise = return (Finished, [], b)

data FCRes = SatFC | UnsatFC deriving Eq

solveFuncConstraints :: MonadIO m => State t -> NameGen -> m (Maybe (State t, NameGen))
solveFuncConstraints s@(State { sym_func_constraints = fc }) ng = do
    (r, (s', !ng')) <- runStateNGT (solveFC fc) s ng
    return $ if r == SatFC then Just (s', ng') else Nothing

solveFC :: MonadIO m => FuncConstraints -> StateNGT t m FCRes
solveFC fcs = do
    fcs <- concatMapM unfolADTArgs fcs -- traverseWithKey?
    liftIO $ putStrLn "after unfoldADTArgs"
    undefined

unfolADTArgs :: MonadIO m => FuncRec -> StateNGT t m [FuncRec]
unfolADTArgs (FR { func_constraints = [] }) = return []
unfolADTArgs fr@(FR { func_name = n, func_constraints = fcs@(first_fc:_) }) = do
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
                TyCon n _:_
                    | Just (DataTyCon { data_cons = dcs }) <- HM.lookup n tenv -> do
                        liftIO . putStrLn $ "i = " ++ show i ++ "\nt = " ++ show t ++ "\ndcs = " ++ show dcs
                        -- Create symvolic functions to continue execution along each alternative branch
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
                                    TyUnknown
                                    alts
                            lam_cse = mkLams (zip (repeat TermL) lam_is) cse
                        liftIO . putStrLn $ "case = " ++ show cse
                        liftIO . putStrLn $ "lam_cse = " ++ show lam_cse

                        insertE n lam_cse

                        -- Rewrite constraints
                        let dc_to_cont_funcs = zip (map dc_name dcs) cont_funcs
                            new_fcs = map (\fc ->
                                            let
                                                ith_arg = fc_args fc !! i
                                                Data dc:as = unApp $ inlineVars eenv ith_arg
                                                all_other_args = deleteAt i $ fc_args fc
                                                new_fc = FC { fc_preconds = undefined
                                                            , fc_args = all_other_args ++ as
                                                            , fc_ret = fc_ret fc
                                                            }
                                                f_name = case lookup (dc_name dc) dc_to_cont_funcs of
                                                                Just fn -> fn
                                                                Nothing -> error "unfoldADTArgs: function not found"
                                            in
                                            (f_name, new_fc)
                                          )
                                          fcs

                        concatMapM unfolADTArgs new_fcs
                _ -> error "unfoldADTArgs: expected ADT type"
        Nothing -> return [fr]

deleteAt :: Int -> [a] -> [a]
deleteAt idx xs = lft ++ rgt
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