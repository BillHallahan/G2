{-# LANGUAGE BangPatterns, FlexibleContexts, LambdaCase, MultiWayIf, OverloadedStrings, TupleSections #-}

{-# LANGUAGE ScopedTypeVariables #-}

module G2.Execution.FuncConstraints ( addFuncConstraintReducer
                                    , redFuncConstraint
                                    , solveFuncConstraintsReducer
                                    , limitSolvingFuncConstraintPieces
                                    
                                    , FCCheckRes (..)
                                    , checkFunctionConstraints
                                    , setUpArgReduction ) where

import G2.Config
import G2.Data.Utils
import G2.Execution.NewPC
import G2.Execution.NormalForms
import G2.Execution.Internals.Reducer
import G2.Language as L
import qualified G2.Language.ExprEnv as E
import G2.Language.Monad
import qualified G2.Language.Stack as Stck
import G2.Lib.Printers
import G2.Solver

import Control.Applicative
import Control.Monad
import Control.Monad.Extra
import Control.Monad.IO.Class
import qualified Control.Monad.State.Lazy as SM
import qualified Data.Foldable as F
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import Data.List
import Data.Maybe
import qualified Data.Sequence as S
import Data.Tuple.Extra

import qualified Data.Text as T
import qualified Data.Text.IO as T

-- | A reducer to add higher order functions to the symbolic function constraints for solving later  
addFuncConstraintReducer :: (Solver solver, Simplifier simplifier, MonadIO m) =>
                             solver
                         -> simplifier
                         -> HS.HashSet Name
                         -> Config
                         -> Reducer m Int t
addFuncConstraintReducer solver simplifier no_inline config =
    (mkSimpleReducer (\_ -> 0) (redFuncConstraint solver simplifier no_inline))
        { onAccept = \s b fc_count -> do
            if print_num_nrpc config
                then liftIO . putStrLn $ "Func Constraints Generated: " ++ show fc_count
                else return ()
            return (s, b) }

{- Note [Evaluating fc_!!_ret variables]

A tricky situation can occur when we have function constraints with preconditions.
Suppose we have a function constraint:
    f x x = r
where x is bound in the expression environment to:
    x -> g y
where g is also a symbolic variable.

If we need to reduce the arguments of f, we will rewrite the function constraints to:
    f (case fr_branch1 of 1 -> ?; 2 -> v_wrap1) (case fr_branch2 of 1 -> ?; 2 -> v_wrap2) = r
where in the expression enviroment we then have:
    x -> g y
    v_wrap1 -> x
    v_wrap2 -> x
Suppose we reduce v_wrap1 before v_wrap2. When we evaluate v_wrap1, we will end up with a new function constraint
for g y:
    f (case fr_branch1 of 1 -> ?; 2 -> v_wrap1) (case fr_branch2 of 1 -> ?; 2 -> v_wrap2) = r
    fr_branch1 = 2 = 3 => g y = r2
Note that setting fr_branch1 to 2 now requires that we also ensure that g y = r2
In the environement, we will then have:
    x -> r2
    v_wrap1 -> x
    v_wrap2 -> x
Note that x is now mapped directly to r2 via sharing. Thus, if we are not careful, we risk
reduction of v_wrap2 not modifying the set of function constraints at all.
This would then allow v_wrap2 to use the result of evaluating `g y` without actually enforcing
the function constraint on g y.

To avoid this problem, whenever we are reducing an expression in a function constraint,
and we evaluate a variable that was introduced by a function constraint, we
duplicate the constraint for that variable, but modify the precondition.
In the running example, we would get:

    f (case fr_branch1 of 1 -> ?; 2 -> v_wrap1) (case fr_branch2 of 1 -> ?; 2 -> v_wrap2) = r
    fr_branch1 = 2 \/ fr_branch2 = 2 = 3 => g y = r2
-}

redFuncConstraint :: (Solver solver, Simplifier simplifier, MonadIO m) =>
                     solver
                  -> simplifier
                  -> HS.HashSet Name
                  -> RedRules
                     m
                     Int
                     t
redFuncConstraint _ _ _ fc_count s@(State { curr_expr = CurrExpr Evaluate (Var (Id n _))
                                          , sym_func_constraints = fcs
                                          , solving_sym_func_constraints = solving_sfc }) b 
    -- See Note [Evaluating fc_!!_ret variables]
    | nameOcc n == nameOcc fcRetName = do
        let fcs' = HM.map (concatMap adjustFC) fcs
            
            new_pre = getPreConds solving_sfc

            adjustFC fc@(FC { fc_ret = Var (Id rn _) })
                | rn == n = [fc { fc_preconds = new_pre }, fc]
            adjustFC fc = [fc]

            s' = s { sym_func_constraints = fcs'}
        return (Finished, [(s', fc_count)], b)
redFuncConstraint solver simplifier no_inline fc_count s b =
    case addFuncConstraints s (name_gen b) of
        Just (s', ng') -> do
            unif_s_ng <- runNamingT (unifyFuncConstraints solver simplifier no_inline s') ng'
            case unif_s_ng of
                (Just s'', ng'') -> do
                    let (xs, ng''') = addFuncArgStates s ng''
                    return (Finished, [(s'', fc_count + 1)] ++ map (,fc_count) xs, b { name_gen = ng''' })
                _ -> return (Finished, [], b { name_gen = ng' })
        Nothing -> return (Finished, [(s, fc_count)], b)

addFuncConstraints :: State t
                   -> NameGen
                   -> Maybe (State t, NameGen)
addFuncConstraints s@(State { expr_env = eenv
                            , tyvar_env = tv_env
                            , curr_expr = CurrExpr _ ce
                            , solving_sym_func_constraints = solving_sfc
                            , sym_func_constraints = sym_fc }) 
                   ng
    |  v@(Var (Id n t)):es_ce <- unApp ce
    , isTyFun t
    , E.isSymbolic n eenv 
    
    , let (ae, stck') = allApplyFrames (exec_stack s)
    , let es = es_ce ++ ae
    , not . isTyFun . typeOf tv_env . mkApp $ v:es_ce =
        let
            (ret_id, ng') = freshSeededId fcRetName (returnType t) ng
            fc = FC { fc_preconds = getPreConds solving_sfc
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

fcRetName :: Name
fcRetName = Name "fc_!!_ret" Nothing 0 Nothing

getPreConds :: FCStatus -> [Expr]
getPreConds (SolvingFCs is_lits) =
    map (\(i, l) -> mkApp $ [Prim Eq TyUnknown, Var i, Lit l]) is_lits
getPreConds InitialRun = []
getPreConds SolvedFCs = []

allApplyFrames :: Stck.Stack Frame -> ([Expr], Stck.Stack Frame)
allApplyFrames stck = go [] stck stck
    where
        go aes pop_stck stck_top_ups
                    | Just (ApplyFrame ae, stck') <- Stck.pop pop_stck = go (ae:aes) stck' stck'
                    | Just (UpdateFrame _, stck') <- Stck.pop pop_stck = go aes stck' stck_top_ups
                    | otherwise = (reverse aes, stck_top_ups)

addFC :: Name -> FuncConstraint -> FuncConstraints -> FuncConstraints
addFC n fc = HM.insertWith (++) n [fc]

------------------------------------------------------------------------------
-- Unifying equal function constraints
------------------------------------------------------------------------------

data UnifyRes r = Unifiable r -- ^ Constraints are unifiable. I.e. function arguments are the same,
                              -- and some kind of result of unification
                | NotUnifiable -- ^ Constraints are not unifiable- function arguments differ
                | Contradiction -- ^ Constraints are contradictory- function arguments are identical, RHS differs in an irresolvable way

unifiableFuncConstraints :: HS.HashSet Name -- ^ Names not to inline
                         -> ExprEnv
                         -> KnownValues
                         -> FuncConstraint
                         -> FuncConstraint
                         -> UnifyRes (S.Seq (Id, Expr), Expr) -- ^ Unifiable if Ids are made equal to corresponding Exprs, and Expr is asserted
unifiableFuncConstraints no_inline eenv kv fc1 fc2 = do
    case all (uncurry (eqUpToTypesInlineIgnoringTicks no_inline eenv)) $ zip (fc_args fc1) (fc_args fc2) of
        True ->
            case alignRet eenv (fc_ret fc1) (fc_ret fc2) of
                Just eq_hs ->
                    let
                        and1 = foldr (\e1 e2 -> mkApp [Prim And TyUnknown, e1, e2]) (mkTrue kv) $ fc_preconds fc1
                        and2 = foldr (\e1 e2 -> mkApp [Prim And TyUnknown, e1, e2]) (mkTrue kv) $ fc_preconds fc2
                        precond_eq = mkApp [Prim Eq TyUnknown, and1, and2]
                    in
                    Unifiable (eq_hs, precond_eq)
                Nothing -> Contradiction
        False -> NotUnifiable

alignRet :: ExprEnv -> Expr -> Expr -> Maybe (S.Seq (Id, Expr))
alignRet eenv (Var i1@(Id n1 _)) e2
    | Just (E.Sym _) <- cs1 = Just $ S.singleton (i1, e2)
    | Just (E.Conc e1) <- cs1 = alignRet eenv e1 e2
    where
        cs1 = E.lookupConcOrSym n1 eenv 
alignRet eenv e1 (Var i2@(Id n2 _))
    | Just (E.Sym _) <- cs2 = Just $ S.singleton (i2, e1)
    | Just (E.Conc e2) <- cs2 = alignRet eenv e1 e2
    where
        cs2 = E.lookupConcOrSym n2 eenv 
alignRet eenv (App e1 e1') (App e2 e2') = do
    r1 <- alignRet eenv e1 e2
    r2 <- alignRet eenv e1' e2'
    return $ r1 <> r2
alignRet _ (Type _) (Type _) = Just mempty
alignRet _ (Data dc1) (Data dc2) | dc_name dc1 == dc_name dc2 = Just mempty
                                 | otherwise = Nothing
alignRet _ (Lit l1) (Lit l2) | l1 == l2 = Just mempty
                             | otherwise = Nothing
alignRet _ _ _ = Nothing

unifyFC :: (Solver solver, Simplifier simplifier, MonadIO m) =>
           solver
        -> simplifier
        -> HS.HashSet Name -- ^ Names not to inline
        -> State t
        -> FuncConstraint
        -> FuncConstraint
        -> NameGenT m (UnifyRes (State t)) -- ^ A state with the function constraints unified, or Nothing if the function constraints are contradicton
unifyFC solver simplifier no_inline s@(State { expr_env = eenv, known_values = kv, tyvar_env = tv_env }) fc1 fc2 = do
    case unifiableFuncConstraints no_inline eenv kv fc1 fc2 of
        Unifiable (eq_hs, precond_eq) -> do
            let eenv' = foldl' addToExprEnv (expr_env s) eq_hs
                new_pcs = ExtCond precond_eq True:(mapMaybe newPC $ F.toList eq_hs)
                s' = s { expr_env = eenv' }
            -- r <- liftIO $ check solver s' (path_conds s')
            ng <- nameGen
            r <- liftIO $ addPCsToState KeepUnknown solver simplifier ng s' [] new_pcs
            case r of
                    Just (end_ng, s'') -> do
                        putNameGen end_ng
                        return $ Unifiable s''
                    Nothing -> return Contradiction
        NotUnifiable -> return NotUnifiable
        Contradiction -> return Contradiction
    where
        newPC (i, e) | isPrimType (typeOf tv_env i) =
            let eq_prim = mkApp [Prim Eq TyUnknown, Var i, inlineVars eenv e] in
                Just $ ExtCond eq_prim True
            | otherwise = Nothing

        addToExprEnv eenv_ (i, e)
            | isPrimType (typeOf tv_env i) = eenv_
            | Var i' <- e, idName i == idName i' = eenv_
            | otherwise = E.insert (idName i) e eenv_

unifyFCList :: (Solver solver, Simplifier simplifier, MonadIO m) =>
               solver
            -> simplifier
            -> HS.HashSet Name -- ^ Names not to inline
            -> State t
            -> [FuncConstraint]
            -> NameGenT m (Maybe (State t, [FuncConstraint])) -- ^ A state with function constraints unified and an updated list of function constraints,
                                                        -- or Nothing if the function constraints are contradicton
unifyFCList solver simplifier no_inline = go []
    where
        go passed_fcs s [] = return . Just $ (s, passed_fcs)
        go passed_fcs s (fc:fcs) = do
            r <- go' s fc fcs
            case r of
                Unifiable s' -> go passed_fcs s' fcs
                Contradiction -> return Nothing
                NotUnifiable -> go (fc:passed_fcs) s fcs

        go' _ _ [] = return NotUnifiable
        go' s fc1 (fc2:fcs) = do
            r <- unifyFC solver simplifier no_inline s fc1 fc2
            case r of
                Unifiable s' -> return $ Unifiable s'
                Contradiction -> return Contradiction
                NotUnifiable -> go' s fc1 fcs

unifyFuncConstraints :: (Solver solver, Simplifier simplifier, MonadIO m) =>
                        solver
                     -> simplifier
                     -> HS.HashSet Name -- ^ Names not to inline
                     -> State t
                     -> NameGenT m (Maybe (State t)) -- ^ A state with function constraints unified, or Nothing if the function constraints are contradictory
unifyFuncConstraints solver simplifier no_inline s@(State { sym_func_constraints = fcs }) = do
    (rs, rfcs) <- mapAccumM (\may_s fc -> do
                        case may_s of
                            Just s_ -> do
                                unif_r <- unifyFCList solver simplifier no_inline s_ fc
                                case unif_r of
                                    Just (s_', fc') -> return (Just s_', fc')
                                    Nothing -> return (Nothing, fc)
                            Nothing -> return (Nothing, fc)
                        ) (Just s) fcs
    return $ fmap (\s' -> s' { sym_func_constraints = rfcs }) rs

------------------------------------------------------------------------------
-- Solving Function Constraints
------------------------------------------------------------------------------


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
-- To solve a set of function constraints, we unfold functions based on ADTs, and then try to solve for literal values.
-- unfoldADT functions instantiates a function definition to branch on an ADt:
--
-- 1) unfoldADTArgs - Check if an argument is a WHNF ADT in all function constraints, if so use it to introduce a branch in the functuon.
--
-- Many of the other functions can then be seen as essentially trying to allow unfoldADTArgs to split up functions
--
-- 2) replaceADTSymVars - Replace symbolic variables with ADT types with a case statement on a symbolic int, where
--    each branch returns a different constructor of that ADT, with symbolic arguments.
--
-- 3) caseToPreCond - We look for arguments that are case constructs introduced in step 2, then translate them into a pair of function constraints
--    that we do in (2).  
--
-- 4) splitWHNFAndNonWHNF - extracts literal arguments into predicate checks, with the goal of dividing constraints
--    wgere some arguments is in WHNF from those constraints in which it is not in WHNF.
--
-- We then must consider branching on literal values. This is done by the `solveLitVals` function.
-- We first introduce splits for different ADT constructors being returned, via the `splitReturns` function.
-- If we have two constraints returning ADT symbolic variables, we unify the symbolic variables.
-- We then solve for functions over just literals using an SMT solver and the theory of uninterpreted functions.
-- Note that solveLitVals may eliminate the possibility of splits on ADTs. For example, if we have:
--     f 1# [] = A
--     f 1# (x:xs) = B
-- Clearly we would want to branch on the list, and (trying to) branching on the literal value will not work.
-- For this reason, we introduce these branches before trying to solve literal constraints,
-- but then revert these branches before we go back to introducing further splits on ADTs.


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

solveFuncConstraintsReducer :: (ASTContainer t Expr, Solver solver, Simplifier simplifier, MonadIO m) => FCLogging -> solver -> simplifier -> HS.HashSet Name -> Reducer m () t
solveFuncConstraintsReducer fc_logging solver simplifier no_inline = mkSimpleReducer (\_ -> ()) go
    where
        go _ s b
            | true_assert s = do
                fc_check_res <- checkFunctionConstraints fc_logging solver simplifier no_inline s (name_gen b)
                case fc_check_res of
                    FCSat s' ng' -> return (Finished, [(s', ())], b { name_gen = ng' })
                    FCReductionNeeded is s' ng' ->
                        case setUpArgReduction is s' of
                            Nothing -> return (Finished, [], b)
                            Just s'' -> return (Finished, [(s'', ())], b { name_gen = ng' })
                    FCUnsat -> return (Finished, [], b)
            | otherwise = return (Finished, [], b)

data FCCheckRes t = FCSat (State t) !NameGen
                  | FCReductionNeeded [(VarLitEqualities, Id)] (State t) !NameGen
                  | FCUnsat

checkFunctionConstraints :: (ASTContainer t Expr, Solver solver, Simplifier simplifier, MonadIO m) =>
                            FCLogging
                         -> solver
                         -> simplifier
                         -> HS.HashSet Name -- ^ Names to not inline
                         -> State t
                         -> NameGen
                         -> m (FCCheckRes t)
checkFunctionConstraints fc_logging solver simplifier no_inline s ng = do
    (m_unif_s, ng') <- runNamingT (unifyFuncConstraints solver simplifier no_inline s) ng
    case m_unif_s of
        Just unif_s -> do
            r <- solveFuncConstraints fc_logging solver simplifier unif_s ng'
            -- liftIO . putStrLn $ case r of Just _ -> "Just"; Nothing -> "Nothing"
            case r of
                Just (s', ng'') -> return $ FCSat s' ng''
                Nothing -> do
                    -- Function constraints were not solved
                    ((is, fc'), (s', !ng'')) <- runStateNGT (do
                        let fcs = sym_func_constraints s
                        -- Add extra calls to higher order functions
                        added_higher_fcs <- mapM (uncurry addHigherOrderCalls) $ HM.toList fcs
                        let fc_higher_reassembled = HM.fromList added_higher_fcs

                        -- Gather unreduced expressions in the function constraints, and set up state to reduce them
                        fc_wrapper <- addWrappersToFC fc_higher_reassembled
                        non_red_v <- collectNonReducedVars fc_wrapper
                        return (non_red_v, fc_wrapper)
                        ) s ng'
                    let s'' = s' { sym_func_constraints = fc' }
                    return $ FCReductionNeeded is s'' ng''
        Nothing -> return FCUnsat

setUpArgReduction ::  [(VarLitEqualities, Id)] -> State t -> Maybe (State t)
setUpArgReduction [] _ = Nothing
setUpArgReduction ((head_whnf_brs, head_i):tail_is) s =
    let
        ce = curr_expr s
        stck = foldl'
                (\st (whnf_brs, i) -> 
                    Stck.push (CurrExprFrame (UpdateSolvingFCs $ SolvingFCs whnf_brs) (CurrExpr Evaluate $ Var i)) st
                )
                (Stck.push (CurrExprFrame (UpdateSolvingFCs InitialRun) ce) (exec_stack s) )
                tail_is
    in
    Just $ s { curr_expr = CurrExpr Evaluate (Var head_i)
             , exec_stack = stck
             , solving_sym_func_constraints = SolvingFCs head_whnf_brs }

------------------------------------------------------------------------------
-- Collecting expressions to reduce when solving fails
------------------------------------------------------------------------------

-- | Expands function definitions to include extra calls to higher order functions.
addHigherOrderCalls :: MonadIO m => Name -> [FuncConstraint] -> StateNGT t m (Name, [FuncConstraint])
addHigherOrderCalls n [] = return (n, [])
addHigherOrderCalls n fcs@(first_fc:_) = do
    tv_env <- tyVarEnv

    extract_higher_order <- extractAll fcs
    -- func_ext_paths <- mapM getFuncExtractorPaths $ concatMap fc_args fcs
    -- liftIO . mapM_ print $ func_ext_paths

    let arg_ts = map (typeOf tv_env) $ fc_args first_fc
        -- (func_inds, higher_tys) = unzip . filter (isTyFun . snd) $ zip [0..] arg_ts
        -- func_ext = map (\i -> \expr_list -> expr_list !! i) func_inds
        (func_ext, higher_tys) = unzip extract_higher_order
    
    case func_ext of
        [] -> return (n, fcs)
        (_:_) -> do
            let ret_ty = typeOf tv_env $ fc_ret first_fc
                higher_ret_ty = map returnType higher_tys
                t_new = mkTyFun $ arg_ts ++ higher_ret_ty ++ [ret_ty]

            -- Update definition of original symbolic function.
            f_new <- freshSeededIdN (Name "f_h" Nothing 0 Nothing) t_new
            insertSymbolicE f_new

            lam_is <- freshIdsN (map (typeOf tv_env) $ fc_args first_fc)
            higher_args_apps <- mapM (\f_ext -> do
                let i = f_ext $ map Var lam_is
                    ts = anonArgumentTypes $ typeOf tv_env i
                as <- freshIdsN ts
                mapM_ insertSymbolicE as
                return (as, mkApp $ i:map Var as)) func_ext
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
                                        (map (\f_ext -> f_ext as) func_ext)
                                        higher_args
                        in
                        fc { fc_args = as ++ new_as
                           , fc_split_on = fc_split_on fc ++ map (const NoSplit) new_as }
                        ) fcs

            return (idName f_new, fcs')

-- | We denote a "path" through a specific shape of a nested data structure as a list
-- of constructors and argument numbers to follow.
type DCPath = [DCPathPiece]

data DCPathPiece = PathStep
                    DataCon -- ^ Constructor
                    Int -- ^ Argument to follow
                | PathFunc
                    Type -- ^ Higher order function type
            deriving (Eq, Show) 

-- | Given an expression, returns a list of paths mapping to (possibly nested) higher order functions.
getFuncExtractorPaths :: Monad m => Expr -> StateNGT t m [DCPath]
getFuncExtractorPaths init_e = do
    tv_env <- tyVarEnv
    return $ go tv_env [] init_e
    where
        go tv_env curr_path e 
            | (Data dc:es) <- unApp e =
                let
                    paths = zipWith (\i ar -> (i, go tv_env curr_path ar)) [0..] $ filter (not . isType) es
                in
                concatMap (\(i, ps) -> map (PathStep dc i:) ps) paths
            | let t = typeOf tv_env e
            , isTyFun t = [curr_path ++ [PathFunc t]]
            | otherwise = []

-- | Turn a DC path into a function, which either calls a higher order function at the given location,
-- or returns a constant (represented as a symbolic variables) 
dcPathsToExtractors :: Monad m => DCPath -> StateNGT t m (Expr -> Expr)
dcPathsToExtractors dc_path 
    | PathFunc t <- last dc_path = do
        const_ret_val <- freshSeededIdN (Name "const" Nothing 0 Nothing) (returnType t)
        insertSymbolicE const_ret_val
        
        lam_is <- freshIdsN (anonArgumentTypes t)
        func_body <- toFunc (returnType t) lam_is (Var const_ret_val) dc_path
        return $ \e -> mkLams (zip (repeat TermL) lam_is) (func_body e)
    | otherwise = error "dcPathsToExtractors: impossible"
    where
        toFunc _ _ _ [] = error "dcPathsToExtractors: impossible"
        toFunc _ lam_is _ [PathFunc _] = do
            return $ \e -> mkApp $ e:map Var lam_is
        toFunc ret_t lam_is const_ret_val (PathStep dc i:xs) = do
            bindee <- freshIdN (dc_type dc)

            dc_binders <- freshIdsN (anonArgumentTypes $ dc_type dc)
            ext <- toFunc ret_t lam_is const_ret_val xs
            let alts = [ Alt (DataAlt dc dc_binders) $ ext (Var $ dc_binders !! i)
                       , Alt Default const_ret_val ]

            return $ \e -> 
                      Case
                        e
                        bindee
                        ret_t
                        alts
        toFunc _ _ _ (PathFunc _:_) = error "dcPathsToExtractors: PathFunc in middle of list"

extractAll :: MonadIO m => [FuncConstraint] -> StateNGT t m [([Expr] -> Expr, Type)]
extractAll fcs = do
    let matched_args = transpose $ map fc_args fcs
    exts <- zipWithM (\i as -> do
        paths :: [DCPath] <- return . nub =<< concatMapM getFuncExtractorPaths as
        extract_expr:: [Expr -> Expr] <- mapM dcPathsToExtractors paths
        let higher_tys = map (\case (PathFunc t) -> t; _ -> error "extractAll: PathFunc expected") $ map last paths
            extract_expr_list = map (\f -> (\es -> f $ es !! i)) extract_expr
        return $ zip extract_expr_list higher_tys
        ) [0..] matched_args
    return $ concat exts

-- | Get expressions that have not been fully reduced. 
collectNonReducedVars :: Monad m => FuncConstraints -> StateNGT t m [(VarLitEqualities, Id)]
collectNonReducedVars fcs = do
    eenv <- exprEnv

    let collect seen whnf_br (Var i@(Id n _))
            | n `notElem` seen
            , Just e <- E.lookup n eenv
            , isExprValueForm eenv e || isWHNFCase e = collect (HS.insert n seen) whnf_br e
            | E.isSymbolic n eenv = []
            | otherwise = [(whnf_br, i)]
        collect seen whnf_br (Case (Var i@(Id n _)) _ _ [Alt _ _, Alt _ e])
            | nameOcc n == whnfBrOccName = collect seen ((i, LitInt 2):whnf_br) e
        collect seen whnf_br e
            | Data _:es <- unApp e = concatMap (collect seen whnf_br) es
        collect _ _ _ = []
    
    return . concatMap (
                    concatMap (concatMap (collect HS.empty []) . fc_args)
             )
           $ HM.elems fcs
    where
        isWHNFCase (Case (Var (Id n _)) _ _ [Alt _ _, Alt _ _]) = nameOcc n == whnfBrOccName
        isWHNFCase _ = False

addWrappersToFC :: Monad m => FuncConstraints -> StateNGT t m FuncConstraints
addWrappersToFC =
    mapM (
            mapM (\fc -> do
                as' <- SM.evalStateT (mapM addVarWrappers $ fc_args fc) HS.empty
                return $ fc { fc_args = map fst as' }
            )
         )

-- Replace any non-WHNF expression with a variable that points to that non-WHNF epxression.
addVarWrappers :: Monad m => Expr -> SM.StateT (HS.HashSet Name) (SM.StateT (State t, NameGen) m) (Expr, Expr)
addVarWrappers c@(Case v@(Var (Id n _)) bindee t [alt1@(Alt _ _), Alt lit_alt e2@(Var (Id br_v _))])
    | nameOcc n == whnfBrOccName = do
        eenv <- SM.lift exprEnv
        m_e <- SM.lift $ lookupE br_v
        case m_e of
            Just e | isExprValueForm eenv e -> do
                e2' <- addVarWrappers e2
                return (Case v bindee t [alt1, Alt lit_alt $ fst e2'], snd e2')
            _ -> return (c, c)
addVarWrappers e
    | d@(Data _):es <- unApp e = do
        es' <- mapM addVarWrappers es
        return (mkApp $ d:map fst es', mkApp $ d:map snd es')
addVarWrappers v@(Var (Id n t)) = do
    seen <- SM.get
    eenv <- SM.lift $ exprEnv
    tv_env <- SM.lift $ tyVarEnv
    case E.lookupConcOrSym n eenv of
        Just (E.Conc e) | n `notElem` seen -> do
            SM.put $ HS.insert n seen
            (e', var) <- addVarWrappers e

            -- Replace each occurence of the variable v with a lambda application returning v:
            --      (\() -> v) ()
            -- Ensures that we evaluate every sub expression before using it to terminate in the function constraint solver
            --
            -- We do NOT do this if we have a primitive type, since primitive expressions are certainly in WHNF, and we do not
            -- want Lambdas/Units leaking into path constraints.
            case isPrimType t of
                True -> return ()
                False -> do
                    unit_dc <- SM.lift mkDCUnitE
                    app_unit_i <- SM.lift $ freshSeededIdN (Name "u" Nothing 0 Nothing) (typeOf tv_env unit_dc)
                    let app_lam = App (Lam TermL app_unit_i var) (Data unit_dc)
                    SM.lift $ mapE (replaceVar n app_lam)

            SM.lift $ insertE n var
            return (e', var)
        _ -> return (v, v)
addVarWrappers e = do
    eenv <- SM.lift $ exprEnv
    case isExprValueForm eenv . stripAllTicks $ inlineVars eenv e of
        True -> return (e, e)
        False -> do
            tv_env <- SM.lift $ tyVarEnv
            dc_false <- SM.lift $ mkFalseE

            red_br <- SM.lift $ freshSeededIdN (Name whnfBrOccName Nothing 0 Nothing) TyLitInt
            SM.lift $ insertSymbolicE red_br
            SM.lift $ insertPCStateNG (ExtCond (mkApp $ [Prim Le TyUnknown, Lit (LitInt 1), Var red_br]) True)
            SM.lift $ insertPCStateNG (ExtCond (mkApp $ [Prim Le TyUnknown, Var red_br, Lit (LitInt 2)]) True)
            -- SM.lift $ insertPCStateNG (ExtCond (mkApp $ [Prim Eq TyUnknown, Var red_br, Lit (LitInt 2)]) True) -- TODO: CUT THIS

            let t = typeOf tv_env e
            i <- SM.lift $ freshSeededIdN (Name "v_wrap" Nothing 0 Nothing) t
            SM.lift $ insertE (idName i) e
            let cse = Case
                        (Var red_br)
                        red_br
                        t
                        [ Alt (LitAlt $ LitInt 1) (Assume Nothing dc_false (Prim UnspecifiedOutput TyBottom)) -- e
                        , Alt (LitAlt $ LitInt 2) (Var i) ] 
            return (cse, Var i)

whnfBrOccName :: T.Text
whnfBrOccName = "red_G2_!!_br"

-- | When solving sub-expressions of function constraints, only do a limited amount of evaluation.
-- This ensures that we do not get stuck looping on evaluation of an infinite expression.
limitSolvingFuncConstraintPieces :: Monad m => Int -> Reducer m Int t
limitSolvingFuncConstraintPieces stps = mkSimpleReducer (\_ -> stps) go
    where
        go 0 s b | SolvingFCs _ <- solving_sym_func_constraints s =
            let
                (e, eenv, stck) = collapseStack (exec_stack s) (expr_env s) (getExpr s)
                s' = s { curr_expr = CurrExpr Return e
                       , expr_env = eenv
                       , exec_stack = stck }
            in
            return (Finished, [(s', stps)], b)
        go !c s b 
            | SolvingFCs _ <- solving_sym_func_constraints s
            , Stck.null (exec_stack s)
            , CurrExpr Return _ <- curr_expr s = return (Finished, [(s, stps)], b)
            | SolvingFCs _ <- solving_sym_func_constraints s = return (InProgress, [(s, c - 1)], b)
        go _ s b = return (NoProgress, [(s, stps)], b)

collapseStack :: Stck.Stack Frame -> ExprEnv -> Expr -> (Expr, ExprEnv, Stck.Stack Frame)
collapseStack stck eenv e
    | Just (CaseFrame i t as, stck') <- fr = collapseStack stck' eenv (Case e i t as)
    | Just (ApplyFrame e', stck') <- fr = collapseStack stck' eenv (App e e')
    | Just (UpdateFrame n, stck') <- fr =
        -- Update frames require a bit of care: we want to avoid a scenario where we overwrite a variable definition
        -- with a reference to itself (i.e. if the current expression is a variable `v`, and we have an update frame for `v`,
        -- we don't want to insert `v -> v` in the environment.)
        case e of
            (Var (Id n' _)) | n == n' -> collapseStack stck' eenv e
            _ -> collapseStack stck' (E.insert n e eenv) e
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

type FCState t m a = SM.StateT (State t, NameGen) (SM.StateT (FCProgress, PrettyGuide, FCLogging) m) a

getProgress :: Monad m => FCState t m FCProgress
getProgress = SM.lift (SM.get >>= return . fst3)

resetProgress :: Monad m => FCState t m ()
resetProgress = SM.lift $ SM.modify (\(_, pg, fc_log) -> (NoProgressFC, pg, fc_log))

madeProgress :: Monad m => FCState t m ()
madeProgress = SM.lift $ SM.modify (\(_, pg, fc_log) -> (MadeProgressFC, pg, fc_log))

solveFuncConstraints :: (ASTContainer t Expr, Solver solver, Simplifier simplifier, MonadIO m) => FCLogging -> solver -> simplifier -> State t -> NameGen -> m (Maybe (State t, NameGen))
solveFuncConstraints fc_logging solver simplifier s@(State { sym_func_constraints = fcs }) ng = do
    let no_tick_s = s { expr_env = stripAllTicks $ expr_env s }
        no_tick_fc = stripAllTicks fcs
    (r, (s', !ng')) <- SM.evalStateT (runStateNGT (startSolveFC solver simplifier (-1) no_tick_fc) no_tick_s ng) (NoProgressFC, mkPrettyGuide no_tick_fc, fc_logging)
    return $ case r of
                    SatFC fcs' -> Just (s' { solving_sym_func_constraints = SolvedFCs
                                           , sym_func_constraints = fcs' }, ng')
                    _ -> Nothing

startSolveFC :: (Solver solver, Simplifier simplifier, MonadIO m) => solver -> simplifier -> Int -> FuncConstraints -> FCState t m FCRes
startSolveFC solver simplifier n fcs = do
    fc_log <- getLogging
    when (fc_log == FCLogging) $ do
        pg <- getPrettyGuide
        liftIO $ do
            putStrLn "------------------------"
            putStrLn "About to call solve FC"
            putStrLn "------------------------"
            putStrLn "Initial FCs:"
            T.putStrLn . addTab $ prettyFuncConstraints pg fcs
    solveFC solver simplifier n fcs


-- TODO: Do we actually need the counter here?
solveFC :: (Solver solver, Simplifier simplifier, MonadIO m) => solver -> simplifier -> Int -> FuncConstraints -> FCState t m FCRes
solveFC _ _ 0 _ = return UnsatFC
solveFC solver simplifier !n fcs = do
    -- Convert functions with only a single constraint into constants
    lit_val_sol <- solveLitVals solver simplifier fcs

    case lit_val_sol of
        True -> return (SatFC fcs)
        False -> do
            resetProgress

            fcs_nosingle <- return . HM.mapMaybe id =<< HM.traverseWithKey solveSingleton fcs

            fcs_simp_pieces <- concatMapM (uncurry simplifyReturns) $ HM.toList fcs_nosingle
            let fc_simp_reassembled = HM.fromListWith (++) fcs_simp_pieces

            -- Replace ADT symbolic variables with case expressions
            mapM_ replaceADTSymVars fc_simp_reassembled

            fcs_precond_arg <- HM.traverseWithKey caseToPreCondArg fc_simp_reassembled
            fcs_precond <- HM.traverseWithKey caseToPreCondRet fcs_precond_arg

            fcs_bool_precond <- HM.traverseWithKey boolToPreCond fcs_precond

            -- Introduce branches on ADTs
            fcs_unfold_adt_pieces <- concatMapM (uncurry unfoldADTArgs) $ HM.toList fcs_bool_precond
            let fc_unfold_adt_reassembled = HM.fromListWith (++) fcs_unfold_adt_pieces


            -- Branch on whether possibly WHNF arguments are reduced or not
            fcs_branch_whnf_pieces <- concatMapM (uncurry branchOnWHNF) $ HM.toList fc_unfold_adt_reassembled
            let fcs_branch_whnf_reassembled = HM.fromListWith (++) fcs_branch_whnf_pieces

            -- Branch on literals, with the aim of splitting up ADTs that are in WHNF from those that are not
            split_whnf_pieces <- concatMapM (uncurry splitWHNFAndNonWHNF) $ HM.toList fcs_branch_whnf_reassembled
            let fc_unfold_split_whnf_reassembled = HM.fromListWith (++) split_whnf_pieces

            elim_non_whnf <- concatMapM (uncurry elimAllNonWHNFOrEquiv) $ HM.toList fc_unfold_split_whnf_reassembled
            let elim_non_whnf_reassembled = HM.fromListWith (++) elim_non_whnf

            prog <- getProgress
            -- liftIO . putStrLn $ "end prog = " ++ show prog

            case prog of
                MadeProgressFC -> solveFC solver simplifier (n - 1) elim_non_whnf_reassembled
                NoProgressFC -> return UnsatFC

-- | If we only have a single function constraint for a given function, we instantiate
-- to a constant function returning the appropriate value.
solveSingleton :: MonadIO m => Name -> [FuncConstraint] -> FCState t m (Maybe [FuncConstraint])
solveSingleton _ [] = return Nothing
solveSingleton n [fc@(FC { fc_args = as, fc_ret = r })] = do
    tv_env <- tyVarEnv

    lam_is <- freshIdsN (map (typeOf tv_env) as)
    let body = mkLams (zip (repeat TermL) lam_is) $ r
    insertE n body
    whenLogging "SolveSingleton" $ do
        pg <- getPrettyGuide
        liftIO $ do
            T.putStrLn . addHalfTab $ "REMOVE SINGLETON FC:"
            T.putStrLn . addTab $ prettyFuncConstraints pg $ HM.singleton n [fc]
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
               , Data dc@(DataCon { dc_name = dc_n, dc_type = dc_ty }):_ <- unApp $ inlineVars eenv r
               , all (sameConstructor eenv dc_n) rs -> do
                    -- Set up the original function to return the required data constructor
                    -- with arguments constructed by fresh symbolic functions 
                    let existing_args = map (typeOf tv_env) $ fc_args fc

                    lam_is <- freshIdsN existing_args
                    let tycon_ts = tyAppArgs $ typeOf tv_env r
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

                    whenLogging "SimplifyReturns" $ do
                        logEEnvInsert n func_def
                        logFCListToNameFCList n fcs new_fcs
                    madeProgress
                    return new_fcs

        _ -> return [(n, fcs)]
    where
        sameConstructor eenv dc_n e
                | Data (DataCon { dc_name = dc_n' }):_ <- unApp $ inlineVars eenv e
                , dc_n == dc_n' = True
                | otherwise = False


-- | We look for arguments that are symbolic variables of ADT types. We then instantiate these symbolic variables to case expressions
--    that branch on a fresh integer variable to choose a constructor with fresh symbolic arguments. For example, if we have:
--        f (xs :: [Int]) = 7
--    where xs is symbolic, we introduce a fresh Int n, and instantiate xs to:
--       xs = case n of
--                1 -> []
--                2 -> y:ys -- y, ys fresh symbolic variables
--    We add a path constraint that `1 <= n <= 2`.
replaceADTSymVars :: MonadIO m => [FuncConstraint] -> FCState t m ()
replaceADTSymVars fcs = do
    eenv <- exprEnv
    tenv <- typeEnv
    tv_env <- tyVarEnv

    mapM_ (\fc -> do 
        mapM_ (go eenv tenv tv_env) (fc_args fc)
        go eenv tenv tv_env $ fc_ret fc) fcs
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
                                        ty_map = HM.fromList $ zipWith (\i it -> (idName i, it)) named_ts tycon_ts
                                        anon_ts = replaceTyVars ty_map $ anonArgumentTypes dc_ty

                                    dc_as <- freshIdsN anon_ts
                                    mapM_ insertSymbolicE dc_as
                                    return . mkApp $ Data dc:map Type tycon_ts ++ map Var dc_as
                            ) dcs
                
                let alts = zipWith Alt (map (LitAlt . LitInt) [1..]) alts_expr
                    cse = Case
                            branch_var
                            (Id bindee TyLitInt)
                            t
                            alts
                    
                    insert_val = case alts_expr of
                                    [a_e] -> a_e
                                    _ -> cse
                insertE n insert_val

                whenLogging "ReplaceSymVars" $ do
                    logEEnvInsert n insert_val
                madeProgress
                return ()

            | otherwise = do
                return ()

-- |  We look for arguments that are case constructs introduced by `replaceADTSymVars`,
-- and we translate constraints into a set of function constraints. For instance if we have a function constraint:
--        f xs = 7
--    and we already have:
--       xs = case n of
--                1 -> []
--                2 -> y:ys -- y, ys fresh symbolic variables
--    we rewrite the constraint to be:
--        n = 1 => f [] = 7
--        n = 2 => f (y:ys) = 7
caseToPreCondArg :: MonadIO m => Name -> [FuncConstraint] -> FCState t m [FuncConstraint]
caseToPreCondArg n = concatMapM go
    where
        go fc@(FC { fc_preconds = pre, fc_args = es }) = do
            eenv <- exprEnv
            let es' = map (getOutCases eenv) es
                case_pats = map getCasePats es'
                m_ind_case_pat = findIndex isJust case_pats
            case m_ind_case_pat of
                Just ind | Just (branch_i, alts) <-case_pats !! ind -> do
                    let eq i = mkApp $ [Prim Eq TyUnknown, Var branch_i, Lit i]
                    
                    let fc_branch = map (\(lit_v, dc) -> fc { fc_preconds = eq lit_v:pre
                                                            , fc_args = replaceAt ind dc es'}) alts

                    whenLogging "CaseToPrecondArg" $ do
                        logFCListToFCList n [fc] fc_branch
                    madeProgress
                    return fc_branch
                    | otherwise -> error "caseToPreCondArg: impossible - index not found"
                Nothing -> return [fc]

caseToPreCondRet :: MonadIO m => Name -> [FuncConstraint] -> FCState t m [FuncConstraint]
caseToPreCondRet n = concatMapM go
    where        
        go fc@(FC { fc_preconds = pre, fc_ret = e }) = do
            eenv <- exprEnv
            let e' = getOutCases eenv e
                m_case_pat = getCasePats e'
            case m_case_pat of
                Just (branch_i, alts) -> do
                    let eq i = mkApp $ [Prim Eq TyUnknown, Var branch_i, Lit i]
                    let fc_branch = map (\(lit_v, dc) -> fc { fc_preconds = eq lit_v:pre, fc_ret = dc}) alts

                    whenLogging "CaseToPrecondRet" $ do
                        logFCListToFCList n [fc] fc_branch
                    madeProgress
                    return fc_branch
                Nothing -> return [fc]

getOutCases :: ExprEnv -> Expr -> Expr                    
getOutCases eenv v@(Var _) =
    let e = inlineVars eenv v in
    case e of
        cse@(Case _ _ _ (Alt (LitAlt _) _:_)) -> cse
        _ -> v
getOutCases _ e = e

getCasePats :: Expr -> Maybe (Id, [(Lit, Expr)])
getCasePats (Case (Var i) (Id _ TyLitInt) _ alts)
    | all (\case (Alt _ (Assume _ _ (Prim UnspecifiedOutput _))) -> False; _ -> True) alts =
                Just (i, map (\case (Alt (LitAlt l) dc) -> (l, dc); _ -> error "getCasePats: expected AltLit") alts)
getCasePats _ = Nothing

-- Look for primitives returning boolean values, and move them into the precondition
boolToPreCond :: MonadIO m => Name -> [FuncConstraint] -> FCState t m [FuncConstraint]
boolToPreCond n fcs = do
    tv_env <- tyVarEnv

    ty_bool <- tyBoolT
    dc_true <- mkDCTrueM
    dc_false <- mkDCFalseM

    boolToPreCond' tv_env ty_bool dc_true dc_false n fcs

boolToPreCond' :: MonadIO m => TyVarEnv -> Type -> DataCon -> DataCon -> Name -> [FuncConstraint] -> FCState t m [FuncConstraint]
boolToPreCond' tv_env ty_bool dc_true dc_false n = concatMapM goArg
    where
        goArg fc@(FC { fc_preconds = pre, fc_args = es }) = do
            eenv <- exprEnv
            let es' = map (getOutPrims eenv) es
                prim_pats = map getPrimPats es'
                m_ind_case_pat = findIndex isJust prim_pats
            case m_ind_case_pat of
                Just ind | Just prim_e <- prim_pats !! ind -> do                    
                    let fc_true = fc { fc_preconds = prim_e:pre
                                     , fc_args = replaceAt ind (Data dc_true) es'}
                        fc_false = fc { fc_preconds = App (Prim Not (TyFun ty_bool ty_bool)) (prim_e):pre
                                      , fc_args = replaceAt ind (Data dc_false) es'}

                    whenLogging "BoolToPreCond" $ do
                        logFCListToFCList n [fc] [fc_true, fc_false]
                    madeProgress
                    return [fc_true, fc_false]
                    | otherwise -> error "boolToPreCond: impossible - index too large"
                Nothing -> return [fc]
                            
        getOutPrims eenv v@(Var (Id _ _)) =
            let e = inlineVars eenv v in
            case unApp e of
                Prim _ _:_ | typeOf tv_env e == ty_bool -> e
                _ -> v
        getOutPrims _ e = e

        getPrimPats e
            | Prim _ _:_ <- unApp e
            , typeOf tv_env e == ty_bool = Just e
        getPrimPats _ = Nothing

-- | Check if there is a function f such that the i^th argument x of that function is an ADT that is WHNF in all constraints.
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
unfoldADTArgs :: MonadIO m => Name -> [FuncConstraint] -> FCState t m [(Name, [FuncConstraint])]
unfoldADTArgs _ [] = return []
unfoldADTArgs n fcs@(first_fc:_) = do
    eenv <- exprEnv
    tenv <- typeEnv
    tv_env <- tyVarEnv

    let ret_ty = typeOf tv_env $ fc_ret first_fc

    -- Find an argument that is (1) an ADT where (2) all arguments are data constructor applications
    let matching_args = transpose $ map fc_args fcs
        all_whnf = findIndex (all (isADT . inlineVars eenv)) matching_args
    case all_whnf of
        Just i | e:_ <- matching_args !! i-> do
            let t = typeOf tv_env e
            
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
                                    bindee
                                    ret_ty
                                    alts
                            lam_cse = mkLams (zip (repeat TermL) lam_is) cse

                        insertE n lam_cse

                        -- Rewrite constraints
                        let dc_to_cont_funcs = zip (map dc_name dcs) cont_funcs
                            new_fcs = map (\fc ->
                                            let
                                                ith_arg = fc_args fc !! i
                                                (dc, as) = case unApp $ inlineVars eenv ith_arg of
                                                                Data dc_:as_ -> (dc_, as_)
                                                                _ -> error "unfoldADTArgs: expected Data"
                                                all_other_args = deleteAt i $ fc_args fc
                                                all_other_split_ons = deleteAt i $ fc_split_on fc

                                                -- If we get new literal values, may be able to do further division on them
                                                -- to split up WHNF/non-WHNF data constructors
                                                new_splits = if any (isPrimType . typeOf tv_env) as
                                                                then map (const NoSplit) all_other_split_ons ++ map (const NoSplit) as
                                                                else all_other_split_ons ++ map (const NoSplit) as

                                                new_fc = FC { fc_preconds = fc_preconds fc
                                                            , fc_args = all_other_args ++ filter (not . isType . inlineVars eenv) as
                                                            , fc_split_on = new_splits
                                                            , fc_ret = fc_ret fc
                                                            }
                                                f_name = case lookup (dc_name dc) dc_to_cont_funcs of
                                                                Just fi -> idName fi
                                                                Nothing -> error "unfoldADTArgs: function not found"
                                            in
                                            (f_name, [new_fc])
                                          )
                                          fcs

                        whenLogging "UnfoldADTArgs" $ do
                            logEEnvInsert n lam_cse
                            logFCListToNameFCList n fcs new_fcs
                        madeProgress
                        return new_fcs
                _ -> error "unfoldADTArgs: expected ADT type"
            | otherwise -> error "unfoldADTArgs: bad index"
        Nothing -> return [(n, fcs)]

branchOnWHNF :: MonadIO m => Name -> [FuncConstraint] -> FCState t m [(Name, [FuncConstraint])]
branchOnWHNF _ [] = return []
branchOnWHNF n fcs@(first_fc:_) = do
    eenv <- exprEnv
    tv_env <- tyVarEnv

    let ret_ty = typeOf tv_env $ fc_ret first_fc

    -- Find an argument that is (1) an ADT where (2) some arguments are wrapped up in WHNF branches
    let matching_args = transpose $ map fc_args fcs
        unspec_case = findIndex (any (isJust . unspecCase . inlineVars eenv)) matching_args
    case unspec_case of
        Just i
            | rel_args <- matching_args !! i
            , whnf_br:_ <- mapMaybe (unspecCase . inlineVars eenv) $ rel_args -> do
            
            -- Adjust function
            lam_is <- freshIdsN (map (typeOf tv_env) $ fc_args first_fc)
            let all_other_is = deleteAt i lam_is
            
            f1 <- freshSeededIdN (Name "elim_unspec" Nothing 0 Nothing) . mkTyFun $ map idType all_other_is ++ [ret_ty]
            f2 <- freshSeededIdN (Name "cont_unspec" Nothing 0 Nothing) . mkTyFun $ map idType lam_is ++ [ret_ty]
            insertSymbolicE f1
            insertSymbolicE f2
            bindee <- freshIdN TyLitInt
            let cse = Case
                        (Var whnf_br)
                        bindee
                        ret_ty
                        [ Alt (LitAlt $ LitInt 1) . mkApp $ Var f1:map Var all_other_is
                        , Alt (LitAlt $ LitInt 2) . mkApp $ Var f2:map Var lam_is ]
                lam_cse = mkLams (zip (repeat TermL) lam_is) cse
            insertE n lam_cse

            -- Rewrite constraints
            let whnf_br_eq_1 = mkApp [Prim Eq TyUnknown, Var whnf_br, Lit (LitInt 1)]
                fcs_can_eq_1 = filter (not . hasIncompatPrecond whnf_br (LitInt 1)) fcs
                fcs_elim = map (\fc -> fc { fc_preconds = whnf_br_eq_1:fc_preconds fc
                                          , fc_args = deleteAt i $ fc_args fc
                                          , fc_split_on = map (const NoSplit) . deleteAt i $ fc_split_on fc }) fcs_can_eq_1

                whnf_br_eq_2 = mkApp [Prim Eq TyUnknown, Var whnf_br, Lit (LitInt 2)]
                fcs_can_eq_2 = filter (not . hasIncompatPrecond whnf_br (LitInt 2)) fcs
                fcs_cont = map (\fc -> fc { fc_preconds = whnf_br_eq_2:fc_preconds fc
                                          , fc_args = map (elimUnspec whnf_br eenv) $ fc_args fc
                                          , fc_split_on = map (const NoSplit ) $ fc_split_on fc }) fcs_can_eq_2

            whenLogging "BranchOnWHNF" $ do
                logEEnvInsert n lam_cse
                logFCListToNameFCList n fcs [(idName f1, fcs_elim), (idName f2, fcs_cont)]
            madeProgress
            return $ [(idName f1, fcs_elim), (idName f2, fcs_cont)]
            | otherwise -> error "branchOnWHNF: Unexpected index or arguments"
        Nothing -> return [(n, fcs)]


    where
        unspecCase (Case (Var whnf_br) _ _ [Alt (LitAlt _) (Assume _ _ (Prim UnspecifiedOutput _)), Alt _ _]) = Just whnf_br
        unspecCase _ = Nothing

        elimUnspec whnf_br eenv e | (Case (Var whnf_br') _ _ [_, Alt _ ae]) <- inlineVars eenv e
                                  , idName whnf_br == idName whnf_br' = ae
        elimUnspec _ _ e = e

hasIncompatPrecond :: Id -- ^ A variable Id
                   -> Lit -- ^ A literal that variable is being assigned to
                   -> FuncConstraint -- ^ An expression to check for incompatability
                   -> Bool
hasIncompatPrecond n l = any (incompatPreCond n l) . fc_preconds 

incompatPreCond :: Id -- ^ A variable Id
                -> Lit -- ^ A literal that variable is being assigned to
                -> Expr -- ^ An expression to check for incompatability
                -> Bool
incompatPreCond (Id n _) l (App (App (Prim Eq _) (Var (Id n' _))) (Lit l')) =
    n == n' && l /= l' -- If the variable names are the same, but different literals, incompatible
incompatPreCond _ _ _ = False

-- | Find an argument that is in WHNF for some function constraints, and not in WHNF for other function constraints,
-- and use the literal values in the constraints to split up these cases into two constraints for two separate functions,
-- one for (only) the WHNF arguments, and one which is also passed the non-WHNF arguments.
--
-- For example, if we have:
--     f 1# (x:xs) = 3#
--     f 2# [] = 4#
--     f z  (g ()) = 5#
-- We introduce a predicate `p :: Int# -> Bool` and adjust the definition of f to be:
--     f l xs = case p l of
--                  True -> f1 l xs
--                  True -> f2 l xs
-- We rewrite the constraints to:
--     p 1# => f1 1# (x:xs) = 3#
--     p 2# => f1 2# [] = 4#
--     not (p 1#) => f2 1# (x:xs) = 3#
--     not (p 2#) => f2 2# [] = 4#
--     not (p z)  => f2 z  (g ()) = 5#
-- We require that ONLY branches where the list is in WHNF be passed to f1- this then allows f1
-- to be unfolded by `unfoldADTArgs`. We allow, though, p to be instantiated to go to f2
-- in any case- this might be needed if, for instance, path constraints force `z = 2#` in the above. 
splitWHNFAndNonWHNF :: MonadIO m => Name -> [FuncConstraint] -> FCState t m [(Name, [FuncConstraint])]
splitWHNFAndNonWHNF _ [] = return []
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
splitWHNFAndNonWHNFIndex _ _ [] = return []
splitWHNFAndNonWHNFIndex i n fcs@(first_fc:_) | fc_split_on first_fc !! i == Split  = return [(n, fcs)]
splitWHNFAndNonWHNFIndex i n fcs@(first_fc:_) = do
    eenv <- exprEnv
    tv_env <- tyVarEnv
    
    let arg_tys = map (typeOf tv_env) $ fc_args first_fc
        ret_ty = typeOf tv_env $ fc_ret first_fc

    lam_is <- freshIdsN (map (typeOf tv_env) $ fc_args first_fc)
    let prim_ty_is = filter (isPrimType . idType) lam_is

    ty_bool <- tyBoolT
    dc_true <- mkDCTrueM
    dc_false <- mkDCFalseM

    f_pred <- freshSeededIdN (Name "pred" Nothing 0 Nothing) . mkTyFun $ map idType prim_ty_is ++ [ty_bool]
    f_true <- freshSeededIdN (Name "f_true" Nothing 0 Nothing) . mkTyFun $ arg_tys ++ [ret_ty]
    f_false <- freshSeededIdN (Name "f_false" Nothing 0 Nothing) . mkTyFun $ arg_tys ++ [ret_ty]

    insertSymbolicE f_pred
    insertSymbolicE f_true
    insertSymbolicE f_false

    bindee <- freshIdN ty_bool
    let pred_app_def = mkApp $ Var f_pred:map Var prim_ty_is
        f_true_app = mkApp $ Var f_true:map Var lam_is
        f_false_app = mkApp $ Var f_false:map Var lam_is
        cse = Case pred_app_def bindee ret_ty
                        [ Alt (DataAlt dc_true []) f_true_app
                        , Alt (DataAlt dc_false []) f_false_app ]
        lam_cse = mkLams (zip (repeat TermL) lam_is) cse

    insertE n lam_cse

    -- Rewrite constraints which do not have argument in WHNF
    non_whnf_cons <- mapMaybeM
                        (\fc -> if | not . isADT . inlineVars eenv $ fc_args fc !! i -> do
                                        -- Add a path constraint that the predicate does not hold
                                        let pred_args = filter (isPrimType . typeOf tv_env) $ fc_args fc
                                            pred_app = mkApp $ Var f_pred:pred_args
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
                                            pred_app = mkApp $ Var f_pred:pred_args
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

    whenLogging "SplitWHNFandNonWHNF" $ do
        logEEnvInsert n lam_cse
        logFCListToNameFCList n fcs $ non_whnf_cons ++ whnf_cons
    madeProgress
    return . HM.toList . HM.fromListWith (++) $ non_whnf_cons ++ whnf_cons

-- | Remove arguments which in all function constraints are either:
--    1) Not in SWHNF
-- or 2) are equivalent.
-- To see why we need this, suppose we have two constraints:
--     f (g x) s = []
--     f (g y) s = x:xs
-- where s is a symbolic variable. These are contradictory, but the only way we can realize this is if
-- we determine that (1) (g x)/(g y) are not helpful, as they are not in SWHNF and (2) s is not useful to branch
-- on, as it is the same in both constraints.
elimAllNonWHNFOrEquiv :: MonadIO m => Name -> [FuncConstraint] -> FCState t m [(Name, [FuncConstraint])]
elimAllNonWHNFOrEquiv _ [] = return []
elimAllNonWHNFOrEquiv n fcs@(first_fc:_) = do
    eenv <- exprEnv
    tv_env <- tyVarEnv

    let matching_args = transpose $ map fc_args fcs

        -- Check if no args are in SWHgNF
        none_whnf = findIndex (\es -> all (not . isRedForm eenv . inlineVars eenv) es) matching_args
        -- Check if all args are the same
        all_same = findIndex (\case es@(head_e:_) -> all (\e -> inlineVars eenv e == inlineVars eenv head_e) es; [] -> False) matching_args

    let ret_ty = typeOf tv_env $ fc_ret first_fc

    case none_whnf <|> all_same of
        Just i -> do            
            lam_is <- freshIdsN (map (typeOf tv_env) $ fc_args first_fc)
            let all_other_is = deleteAt i lam_is
                all_other_vars = map Var all_other_is
                sym_f_ty = mkTyFun $ (map idType all_other_is) ++ [ret_ty]
            
            f <- freshSeededIdN (Name "elim_nonwhnf_f" Nothing 0 Nothing) sym_f_ty
            insertSymbolicE f
            let lam_f = mkLams (zip (repeat TermL) lam_is) . mkApp $ Var f:all_other_vars
            insertE n lam_f

            let new_fcs = map (\fc ->
                                let
                                    all_other_args = deleteAt i $ fc_args fc
                                    all_other_split_ons = deleteAt i $ fc_split_on fc

                                    new_fc = FC { fc_preconds = fc_preconds fc
                                                , fc_args = all_other_args
                                                , fc_split_on = all_other_split_ons
                                                , fc_ret = fc_ret fc
                                                }
                                in
                                new_fc
                                )
                                fcs
            whenLogging "elimAllNonWHNF" $ do
                logEEnvInsert n lam_f
                logFCListToNameFCList n fcs $ [(idName f, new_fcs)]
            -- madeProgress
            elimAllNonWHNFOrEquiv (idName f) new_fcs
        _ -> return [(n, fcs)]
    where
        isRedForm _ (Case _ _ _ [Alt (LitAlt _) (Assume Nothing _ (Prim UnspecifiedOutput _)), Alt _ _]) = True
        isRedForm eenv e = isExprValueForm eenv e

-- | Checks if we can find solutions to all functions.
-- Uses an SMT solver and the theory of uninterpreted functions to solve for literal inputs/outputs.
solveLitVals :: (Solver solver, Simplifier simplifier, MonadIO m) => solver -> simplifier -> FuncConstraints -> FCState t m Bool
solveLitVals solver simplifier fcs = do
    -- We optimistically insert into the ExprEnv throughout this code,
    -- and revert to the old ExprEnv at the end if we fail to find a solution.
    eenv <- exprEnv
    tv_env <- tyVarEnv
    kv <- knownValues

    fcs_split <- splitReturns fcs

    -- let pg = mkPrettyGuide (HM.toList fcs_split)
    -- eenv <- exprEnv
    -- liftIO $ putStrLn $ "fcs_split =\n" ++ T.unpack (prettyFuncConstraints pg $ inlineVars eenv fcs_split)  

    new_pcs <- concatMapM (\(n, fc_list) ->
        case fc_list of
            [] -> return []
            (fc_first:_) -> do
                    let prim_arg_tys = map (typeOf tv_env) $ filter (isPrimType . typeOf tv_env) $ fc_args fc_first
                        call_ty = mkTyFun $ prim_arg_tys ++ [TyLitInt]
                    sel_func <- freshSeededIdN (Name "sel" Nothing 0 Nothing) call_ty

                    let fc_prim = map (\fc -> fc { fc_args = filter (isPrimType . typeOf tv_env) $ fc_args fc}) fc_list
                    (unified_id, fc_unified) <- unifyAllRetSymVars fc_prim
                    -- Filter to only constraints that do not return symbolic variables.
                    -- Constraints returning symbolic variables may return any value; thus they may be ignored.
                    fc_no_sym_ret <- filterM (\fc -> case fc_ret fc of
                                                        (Var (Id vn t)) -> do
                                                            m_conc_or_sym <- deepLookupConcOrSymE vn
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
                    
                    return fc_pcs
            ) (HM.toList fcs_split)
    (s, _) <- SM.get
    -- r <- liftIO $ check solver s pcs'
    ng <- nameGen
    r <- liftIO $ addPCsToState KeepUnknown solver simplifier ng s [] new_pcs
    case r of
            Just (ng', s') -> do
                SM.put (s', ng')
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

-- If the same function is returning different constructors for an ADT, try to split it up using literals.
-- For instance, if we have:
--    f 1# = 2:xs
--    f 2# = []
-- we rewrite this to:
--    f x = case br x of
--               1# -> f1 x:f2 x
--               2# -> []
-- where br, f1, f2, are all fresh variables.
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
splitReturns' _ [] = return []
splitReturns' n fcs@(first_fc:_) = do
    eenv <- exprEnv
    tenv <- typeEnv
    tv_env <- tyVarEnv

    if | let ret_ty_unapp = unTyApp . tyVarSubst tv_env . typeOf tv_env $ fc_ret first_fc
       , TyCon tn _:tycon_ts <- ret_ty_unapp
       , Just (DataTyCon { data_cons = dcs}) <- HM.lookup tn tenv
       , all (isADT . inlineVars eenv . fc_ret) fcs -> do

            let ret_ty = typeOf tv_env $ fc_ret first_fc

            lam_is <- freshIdsN (map (typeOf tv_env) $ fc_args first_fc)
            let prim_ty_is = filter (isPrimType . idType) lam_is

            -- Creating new function definition
            sel <- freshSeededIdN (Name "sel" Nothing 0 Nothing) . mkTyFun $ map idType prim_ty_is ++ [TyLitInt]
            insertSymbolicE sel

            bindee <- freshIdN ret_ty

            dc_funcs <- foldM (\hm (DataCon { dc_name = dc_n, dc_type = dc_ty}) -> do
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
                        let fs = case HM.lookup (dc_name dc) dc_funcs of
                                    Just fs_ -> fs_
                                    Nothing -> error "splitReturns': impossible - function for dc argument not found"
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
                                        _ -> error "splitReturns': impossible - data constructor expected"
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

            whenLogging "SplitReturns" $ do
                logEEnvInsert n lam_cse
                logFCListToNameFCList n fcs $ (idName sel, fcs_sel):fcs_branches
            madeProgress
            return $ (idName sel, fcs_sel):fcs_branches
       | otherwise -> return [(n, fcs)]


isType :: Expr -> Bool
isType (Type _) = True
isType _ = False

deleteAt :: Int -> [a] -> [a]
deleteAt idx xs | (lft, (_:rgt)) <- splitAt idx xs = lft ++ rgt
                | otherwise = error "deleteAt: bad index"

replaceAt :: Int -> a -> [a] -> [a]
replaceAt idx x xs | (lft, (_:rgt)) <- splitAt idx xs = lft ++ [x] ++ rgt
                   | otherwise = error "replaceAt: bad index"

-------------------------------------------------------------------------------
-- Function argument states
-------------------------------------------------------------------------------
addFuncArgStates :: State t -> NameGen -> ([State t], NameGen)
addFuncArgStates s = runNamingM (addFuncArgStates' s)

addFuncArgStates' :: State t -> NameGenM [State t]
addFuncArgStates' s@(State { curr_expr = CurrExpr _ ce, expr_env = eenv, tyvar_env = tv_env })
    |  v@(Var (Id n t)):es_ce <- unApp ce
    , isTyFun t
    , E.isSymbolic n eenv 
    
    , not . isTyFun . typeOf tv_env . mkApp $ v:es_ce = do
        let reach_err = filter (reachesError eenv . snd) $ zip [0 :: Int ..] es_ce
            ret_ty = returnType t
        (s', rep_fn) <- adjustForFuncArg s n es_ce ret_ty
        if null reach_err
            then return []
            else mapM (uncurry (addFuncArgStates'' s' rep_fn es_ce ret_ty)) reach_err
    | otherwise = return []

adjustForFuncArg :: State t -> Name -> [Expr] -> Type -> NameGenM (State t, Name)
adjustForFuncArg s@(State { fc_state_type = PostCall
                          , known_values = kv
                          , expr_env = eenv
                          , sym_func_constraints = fcs
                          , solving_sym_func_constraints = solving_sfc
                          , type_env = tenv
                          , tyvar_env = tv_env }) fn es_ce ret_ty = do
    let ty_bool = tyBool kv
        dc_true = mkDCTrue kv tenv
        dc_false = mkDCFalse kv tenv
    pr <- freshSeededIdN (Name "fa_pred" Nothing 0 Nothing) . mkTyFun $ map (typeOf tv_env) es_ce ++ [ty_bool]
    f1 <- freshSeededIdN (Name "fa_f1" Nothing 0 Nothing) . mkTyFun $ map (typeOf tv_env) es_ce ++ [ret_ty]
    f2 <- freshSeededIdN (Name "fa_f2" Nothing 0 Nothing) . mkTyFun $ map (typeOf tv_env) es_ce ++ [ret_ty]

    lam_is <- freshIdsN (map (typeOf tv_env) es_ce)
    let lam_vars = map Var lam_is
    bindee <- freshIdN ty_bool
    
    let alts = [ Alt (DataAlt dc_true []) (mkApp $ Var f1:lam_vars)
               , Alt (DataAlt dc_false []) (mkApp $ Var f2:lam_vars) ] 
        cse = Case
                (mkApp $ Var pr:lam_vars)
                bindee
                ty_bool
                alts
        lam_cse = mkLams (map (TermL,) lam_is) cse
        eenv' = E.insert fn lam_cse eenv
        eenv'' = E.insertSymbolic pr . E.insertSymbolic f1 . E.insertSymbolic f2 $ eenv'

        -- Adjust func constraints
        fc_fn = fromMaybe [] $ HM.lookup fn fcs

        new_fc_pred = FC { fc_preconds = getPreConds solving_sfc
                         , fc_args = es_ce
                         , fc_ret = Data dc_true
                         , fc_split_on = map (const NoSplit) es_ce}
        adj_fc_pred = map (\fc -> fc { fc_ret = Data dc_false}) fc_fn
        fc_pred = new_fc_pred:adj_fc_pred

        fcs' = HM.insert (idName f2) fc_fn
             $ HM.insert (idName pr) fc_pred
             $ HM.delete fn fcs

    return $ (s { expr_env = eenv'', sym_func_constraints = fcs', fc_state_type = FuncArg }, idName f1)
adjustForFuncArg s fn _ _ = return (s, fn)

addFuncArgStates'' :: State t -> Name -> [Expr] -> Type -> Int -> Expr -> NameGenM (State t)
addFuncArgStates'' s@(State { curr_expr = CurrExpr _ ce
                            , expr_env = eenv
                            , type_env = tenv
                            , tyvar_env = tv_env }) fn es_ce ret_ty i e
    | TyCon tn _:ts <- unTyApp t
    , Just (DataTyCon { data_cons = dcs, bound_ids = bids }) <- HM.lookup tn tenv = do
        let bids_to_ts = HM.fromList $ zip (map idName bids) ts

        cont_funcs <- mapM 
                        (\dc ->
                                let
                                    anon_ts = anonArgumentTypes $ replaceTyVars bids_to_ts (typeOf tv_env dc)
                                    sym_f_ty = mkTyFun $ anon_ts ++ [ret_ty]
                                in
                                freshSeededIdN (Name "sym_f" Nothing 0 Nothing) sym_f_ty
                        ) dcs

        alts <- zipWithM
                    (\dc f -> do
                        let anon_ts = anonArgumentTypes $ replaceTyVars bids_to_ts (typeOf tv_env dc)
                        fs <- freshIdsN anon_ts
                        return $ Alt (DataAlt dc fs) (mkApp $ Var f:map Var fs))
                    dcs cont_funcs

        lam_is <- freshIdsN (map (typeOf tv_env) es_ce)
        let branch_on = lam_is !! i
        bindee <- freshIdN (idType branch_on)
        let cse = Case
                    (Var branch_on)
                    bindee
                    ret_ty
                    alts
            lam_cse = mkLams (zip (repeat TermL) lam_is) cse

        let eenv' = E.insert fn lam_cse eenv
            eenv'' = foldl' (flip E.insertSymbolic) eenv' cont_funcs
        return $ s { curr_expr = CurrExpr Evaluate ce
                   , expr_env = eenv''
                   , exec_stack = Stck.singleton $ CurrExprFrame NoAction (CurrExpr Return $ Prim UnspecifiedOutput TyBottom) }
    | otherwise = error $ "addFuncArgStates'': unsupported " ++ show t
    where t = typeOf tv_env e

reachesError :: ExprEnv -> Expr -> Bool
reachesError eenv = reachesError' eenv HS.empty

reachesError' :: ExprEnv -> HS.HashSet Name -> Expr -> Bool 
reachesError' eenv = go
    where
        go seen (Var (Id n _)) 
            | n `elem` seen = False
            | Just e <- E.lookup n eenv = go (HS.insert n seen) e
            | otherwise = False
        go _ (Prim Raise _) = True
        go _ (Prim Error _) = True
        go _ (Prim Undefined _) = True
        go seen e = any (go seen) $ children e

------------------------------------------------------------------------------
-- Logging
------------------------------------------------------------------------------

updateFCPrettyGuide :: (Monad m, Named a) => a -> FCState t m ()
updateFCPrettyGuide v = SM.lift $ SM.modify (\(prog, pg, fc_log) -> (prog, updatePrettyGuide v pg, fc_log))

getPrettyGuide :: Monad m => FCState t m PrettyGuide
getPrettyGuide = SM.lift (SM.get >>= return . snd3)

getPrettyGuideUpdating :: (Monad m, Named a) => a -> FCState t m PrettyGuide
getPrettyGuideUpdating a = do
    updateFCPrettyGuide a
    getPrettyGuide

getLogging :: Monad m => FCState t m FCLogging
getLogging = SM.lift (SM.get >>= return . thd3)

whenLogging :: MonadIO m => String -> FCState t m () -> FCState t m ()
whenLogging step f = do
    fc_log <- getLogging
    case fc_log of
        FCLogging -> do
            liftIO . putStrLn $ "STEP: " ++ step
            f
        NoFCLogging -> return ()

logEEnvInsert :: MonadIO m => Name -> Expr -> FCState t m ()
logEEnvInsert n e = do
    pg <- getPrettyGuideUpdating (n, e)
    liftIO $ do
        T.putStrLn . addHalfTab $ "EENV Update:"
        T.putStrLn . addTab $ printName pg n <> " -> " <> mkDirtyExprHaskell pg e

logFCListToFCList :: MonadIO m => Name -> [FuncConstraint] -> [FuncConstraint] -> FCState t m ()
logFCListToFCList n init_fcs up_fcs = do
    updateFCPrettyGuide (init_fcs, up_fcs)
    pg <- getPrettyGuide
    let init_fcs_hm = HM.singleton n init_fcs
    let up_fcs_hm = HM.singleton n up_fcs
    liftIO $ do
        T.putStrLn . addHalfTab $ "IN FC:"
        T.putStrLn . addTab $ prettyFuncConstraints pg init_fcs_hm
        T.putStrLn . addHalfTab $ "RES FC:"
        T.putStrLn . addTab $ prettyFuncConstraints pg up_fcs_hm

logFCListToNameFCList :: MonadIO m => Name -> [FuncConstraint] -> [(Name, [FuncConstraint])] -> FCState t m ()
logFCListToNameFCList n init_fcs up_fcs = do
    updateFCPrettyGuide (init_fcs, up_fcs)
    pg <- getPrettyGuide
    let init_fcs_hm = HM.singleton n init_fcs
    let up_fcs_hm = HM.fromListWith (++) up_fcs
    liftIO $ do
        T.putStrLn . addHalfTab $ "IN FC:"
        T.putStrLn . addTab $ prettyFuncConstraints pg init_fcs_hm
        T.putStrLn . addHalfTab $ "RES FC:"
        T.putStrLn . addTab $ prettyFuncConstraints pg up_fcs_hm

addHalfTab :: T.Text -> T.Text
addHalfTab t = "  " <> T.intercalate "\n  " (T.lines t)

addTab :: T.Text -> T.Text
addTab t = "    " <> T.intercalate "\n    " (T.lines t)
