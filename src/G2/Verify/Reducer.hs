{-# LANGUAGE BangPatterns, FlexibleContexts, MultiParamTypeClasses, MultiWayIf, OverloadedStrings, TupleSections #-}

module G2.Verify.Reducer ( VerifierTracker (..)
                         , Goal (..)
                         , isTheorem
                         , initVerifierTracker
                         , prettyVerifierTracker
                         
                         , nrpcAnyCallReducer
                         , adjustFocusReducer
                         , verifySolveNRPC
                         , verifyHigherOrderHandling
                         , unifyNRPCReducer
                         , inconsistentNRPCHalter
                         , approximationHalter

                         , LemmaInfo
                         , emptyLemmaInfo
                         , genLemmaReducer
                         , acceptLemmaReducer
                         
                         , discardOnFalse
                         , currExprIsFalse
                         , currExprIsTrue ) where

import G2.Config
import qualified G2.Data.UFMap as UF
import G2.Data.Utils
import G2.Execution.Reducer
import G2.Interface
import G2.Language
import G2.Language.Approximation
import qualified G2.Language.ExprEnv as E
import G2.Language.ReachesSym
import G2.Language.KnownValues
import qualified G2.Language.Stack as Stck
import qualified G2.Language.Typing as T
import G2.Lib.Printers
import G2.Solver
import G2.Verify.Config
import G2.Verify.StaticArgTrans

import Control.Monad.Extra
import Control.Monad.IO.Class
import qualified Control.Monad.State as SM
import qualified Data.HashSet as HS
import qualified Data.HashMap.Strict as HM
import Data.List
import qualified Data.Map.Lazy as M
import Data.Maybe
import qualified Data.Sequence as Seq
import qualified Data.Text as T
import Data.Traversable

-- | When a newly reached function application is approximated by a previously seen (and thus explored) function application,
-- shift the new function application into the NRPCs.
nrpcAnyCallReducer :: MonadIO m =>
                      HS.HashSet Name -- ^ Names of functions that should not be approximated
                   -> VerifyConfig
                   -> Config
                   -> Reducer m Int VerifierTracker
nrpcAnyCallReducer no_nrpc_names v_config config =
    (mkSimpleReducer (const 0) red)
            { onAccept = \s b nrpc_count -> do
            if print_num_nrpc config
                then liftIO . putStrLn $ "NRPCs Generated: " ++ show nrpc_count
                else return ()
            return (s, b) }

    where        
        red rv s@(State { curr_expr = CurrExpr er ce, expr_env = eenv, tyvar_env = tvnv, track = vt }) b@(Bindings { name_gen = ng })
            | Stck.null . popAppliable $ exec_stack s
            , let stripped_ce = stripNRBT ce
            , (Var (Id vn _)):(_:_) <- unApp stripped_ce
            , let tcf = tail_called_funcs vt
            , vn `notElem` tcf =
                let
                    s' = s { track = vt { tail_called_funcs = HS.insert vn tcf }}
                in
                return (Finished, [(s', rv)], b)

            | maybe True (allowed_frame . fst) (Stck.pop (exec_stack s))
            
            -- Check if we have a symbolic function at the center of the app
            , Var (Id _ t):xs <- unApp $ getExpr s

            -- Calculate arity of function, and wrap it in appropriate number of arguments
            , let arity = length . argumentTypes $ tyVarSubst tvnv t
            , let need_apply = arity - length xs
            , let (wrapped_ce, stck') = applyWrap need_apply (getExpr s) (exec_stack s)

            , let stripped_ce = stripNRBT wrapped_ce
            , v@(Var (Id _ _)):es@(_:_) <- unApp stripped_ce  = do
                -- Convert arguments into NRPCs
                let s' = s { curr_expr = CurrExpr er wrapped_ce, exec_stack = stck' }
                    (s'', ng') = if (arg_rev_abs v_config) == AbsFuncArgs then argsToNRPCs s' (name_gen b) v es else (s', ng)

                -- Given a function call `f x1 ... xn`, we move the entire call to `f` into an NRPC.
                -- Note that createNewCond wraps the function call with a Tick.
                -- This prevents that same function call from being immediately turned back into an NRPC
                -- when it is removed from the NRPCs.
                let nr_s_ng = if
                                -- Line (*) make sure we don't add back to NRPCs immediately.
                                | not (hasNRBT wrapped_ce) -- (*)
                                , allowedApp wrapped_ce eenv tvnv -> createRA ng' (focused s'') s''
                                | otherwise -> Nothing

                case nr_s_ng of
                    Just (nr_s, _, _, ng'') -> return (Finished, [(nr_s, rv + 1)], b { name_gen = ng'' })
                    _ -> return (Finished, [(s'', rv)], b { name_gen = ng' })
            | Tick nl (Var (Id n _)) <- ce
            , isNonRedBlockerTick nl
            , Just e <- E.lookup n eenv = return (Finished, [(s { curr_expr = CurrExpr Evaluate e }, rv)], b)
        red rv s b = return (Finished, [(s, rv)], b)

        -- We only abstract if:
        -- * the function is fully applied (the whole application does not have a function type)
        -- * the function is not in the list of names to not add to NRPCs
        -- * we are not applying a symbolic function
        allowedApp app eenv tvnv
            | Var (Id n _):_:_ <- unApp app
            , Just n' <- E.deepLookupVar n eenv
            , not . isTyFun . typeOf tvnv $ app =
                not (n' `HS.member` no_nrpc_names)
            | Data _:_:_ <- unApp app
            , not . isTyFun . typeOf tvnv $ app
            , data_arg_rev_abs v_config == AbsDataArgs = True
            | otherwise = False
        
        -- Replace each argument which is itself a function call with a NRPC.
        -- For instance:
        --  @ f (g x) y (h z)@
        -- Will get rewritten to:
        --  @ f s1 y s2 @
        -- with new NRPCs:
        --  @ s1 = g x 
        --    s2 = h z @
        -- See Note [Replacing nested function applications]
        argsToNRPCs s ng v es =
            let
                arg_holes = holes es
                ((s', ng'), es') = mapAccumR (\(s_, ng_)  (e_, other_es) -> appArgToNRPC HS.empty s_ ng_ HS.empty e_ other_es) (s, ng) arg_holes
            in
            (s' { curr_expr = CurrExpr Evaluate . mkApp $ v:es' }, ng')
        
        argsToNRPCs' seen s@(State { expr_env = eenv }) ng grace v@(Var (Id n _))
            | n `notElem` seen
            , Just (E.Conc e) <- E.lookupConcOrSym n eenv =
                let
                    (e', s', ng') = argsToNRPCs' (HS.insert n seen) s ng grace e
                    eenv' = E.insert n e' (expr_env s')
                in
                (v, s' { expr_env = eenv' }, ng')
        argsToNRPCs' seen s@(State { expr_env = eenv, tyvar_env = tvnv }) ng grace e@(App _ _)
            | allowedApp e eenv tvnv
            , v:es <- unApp e =
                let
                    arg_holes = holes es
                    grace' = case v of
                                Data _ -> grace
                                _ -> HS.empty 
                    ((s', ng'), es') = mapAccumR
                        (\(s_, ng_) (e_, other_es) -> appArgToNRPC seen s_ ng_ grace' e_ other_es) (s, ng) arg_holes
                    e' = mkApp (v:es')
                in
                case createRAExpr ng' (Unfocused ()) s' e' of
                    Just (s'', sym_i, _, ng'') -> (Var sym_i, s'', ng'')
                    Nothing -> (e', s', ng')
        argsToNRPCs' _ s ng _ e = (e, s, ng)

        -- (Maybe) converts an argument of an application into an NRPC.
        -- `e` is the argument to possible convert, `es` is all other arguments.
        -- If using the shared variable heuristic, see Note [Replacing nested function applications]-
        -- this heuristic means we replace `e` only if some symbolic variable in `e` also occurs in some other
        -- argument in `e`.  The `grace` variable is used to replace arguments through data constructors,
        -- see Note [Data Constructor Arguments to NRPCs]
        appArgToNRPC seen s@(State { expr_env = eenv }) ng grace e other_es
            | let e_symb = symbolic_names eenv e
            , let es_symb = HS.unions (grace:map (symbolic_names eenv) other_es)
            , shared_var_heuristic v_config == NoSharedVarHeuristic || (not . HS.null $ e_symb `HS.intersection` es_symb) = 
                let (e_', s_', ng_') = argsToNRPCs' seen s ng es_symb e in
                ((s_', ng_'), e_')
            | otherwise = ((s, ng), e)

        symbolic_names = symbolic_names' HS.empty

        symbolic_names' seen eenv (Var (Id n _))
            | n `HS.member` seen = HS.empty
            | Just (E.Sym _) <- E.lookupConcOrSym n eenv = HS.singleton n
            | Just (E.Conc e) <- E.lookupConcOrSym n eenv = symbolic_names' (HS.insert n seen) eenv e
        symbolic_names' seen eenv e@(App e1 e2)
            | (Var (Id n _)):es <- unApp e
            , Just stat <- fmap (detStatic n) (E.lookup n eenv)
            , length stat == length es = HS.unions
                                       . map (symbolic_names' seen eenv)
                                       . map snd
                                       . filter (\(s, _) -> s == NonStatic)
                                       $ zip stat es
            | otherwise = symbolic_names' seen eenv e1 `HS.union` symbolic_names' seen eenv e2
        symbolic_names' _ _ _ = HS.empty

        allowed_frame (ApplyFrame _) = False
        allowed_frame _ = True

        applyWrap !need e stck | need > 0, Just (ApplyFrame a, stck') <- Stck.pop stck = applyWrap (need - 1) (App e a) stck'
                               | need > 0, Just (UpdateFrame _, stck') <- Stck.pop stck = applyWrap need e stck'
                               | otherwise = (e, stck)
        
        stripNRBT (Tick nl e) | isNonRedBlockerTick nl = e
        stripNRBT (App e1 e2) = App (stripNRBT e1) e2
        stripNRBT e = e

        hasNRBT (Tick nl e) | isNonRedBlockerTick nl = True
                            | otherwise = hasNRBT e
        hasNRBT (App e1 _) = hasNRBT e1
        hasNRBT _ = False

        popAppliable stck | Just (UpdateFrame _, stck') <- Stck.pop stck = popAppliable stck'
                          | Just (ApplyFrame _, stck') <- Stck.pop stck = popAppliable stck'
                          | Just (CurrExprFrame (EnsureEq _) _, stck') <- Stck.pop stck = popAppliable stck'
                          | otherwise = stck

-- | Create a NRPC if heuristics apply.
createRA :: NameGen -> GenFocus n -> State t -> Maybe (State t, Id, NRPC, NameGen)
createRA ng f s | nrpcHeuristics (expr_env s) (getExpr s) = createNonRed ng f s
                | otherwise = Nothing

createRAExpr :: NameGen -> GenFocus n -> State t -> Expr -> Maybe (State t, Id, NRPC, NameGen)
createRAExpr ng f s e | nrpcHeuristics (expr_env s) e = createNonRed' ng f s e
                      | otherwise = Nothing

-- | Only add RAs if they have an argument that is non-concrete
nrpcHeuristics :: ExprEnv -> Expr -> Bool
nrpcHeuristics eenv = any (reachesSymbolic eenv) . unApp

-- | Note [Replacing nested function applications]
-- Suppose we have a function application:
-- @ f (g xs) (h xs) (j ys) @
-- where `xs` and `ys` are symbolic.
-- If evaluating `g xs` or `h xs`, and thus concretizing `xs`, we want to simultaneously
-- make progress in evaluating BOTH expressions, so that (hopefully) we can eliminate states via an approximation.
-- That is, if we concretize `xs` to `x:xs'`, we are hoping to end up with something like
-- `g xs'` and `h xs'`, rather than `g xs'` and `h (x:xs')`.
--
-- Thus, because these two arguments have a shared variable, we rewrite the application to be:
-- @ f sym1 sym2 (j ys) @
-- with NRPCs:
-- @ sym1 = g xs
--   sym2 = h xs @
-- Note that we do not add an NRPC for `j ys`, because there is only one occurence of the symbolic variable `ys`.

-- Note [Data Constructor Arguments to NRPCs]
-- (See also Note [Replacing nested function applications])
--
-- Consider a function call such as:
-- @ f xs (D (g xs)) @
-- (where `D` is a data constructor.)
-- We never move data constructor applications into NRPCs, but would like to move `g xs` into an NRPC, and get:
-- @ f xs (D sym) @
-- with the NRPC
-- @ sym = g xs @.
-- to allow this, we pass on used variable names from arguments in application layers "above" data constructors
-- via the `grace` variable. Note that in `argsToNRPCs'` we pass on `grace` unchanged if we have a data application,
-- but set it to empty if we have a variable application.  We then include the variables in `grace` when checking
-- if application arguments share symbolic variables with each other.


-- | Handles NRPC focuses:
--   (1) If we evaluate a variable when in a Focused state, set all NRPCs assigning to that variable to Focused.
--   (2) If we have only unfocused NRPCs, empty the NRPCs.
-- See Note [NRPC Focus] in "G2.Language.NonRedPathConds".
adjustFocusReducer :: Monad m => Reducer m () VerifierTracker
adjustFocusReducer = mkSimpleReducer (const ()) red
    where
        -- (1) Adjust variable focus
        red rv s@(State { expr_env = eenv
                        , curr_expr = CurrExpr _ (Var (Id n _))
                        , non_red_path_conds = nrpc
                        , focused = Focused 
                        , track = VT { focus_map = fm }}) b =
            let
                bring_focus = find_focus (HS.singleton n) (HS.singleton n)
                nrpc' = foldr (\n_ -> setFocus n_ Focused eenv) nrpc bring_focus
                s' = s { non_red_path_conds = nrpc' }
            in
            return (Finished, [(s', rv)], b)
            where
                find_focus dig found
                    | HS.null dig = found
                    | otherwise =
                        let
                            found_new = HS.unions . map (fromMaybe HS.empty . flip HM.lookup fm) $ HS.toList dig
                            new_dig = found_new `HS.difference` found
                        in
                        find_focus new_dig (found `HS.union` found_new)
                    
        red rv s@(State { curr_expr = CurrExpr _ (Var (Id n _)) }) b =
            let
                s' = updateStateFocusMap n s
            in
            return (Finished, [(s', rv)], b)
        red rv s@(State { curr_expr = CurrExpr _ e, exec_stack = stck, focused = Focused }) b
            | Just (CurrExprFrame (EnsureEq _) _, _) <- Stck.pop stck =
                let s' = update_ensure_eq HS.empty e s in
                return (Finished, [(s', rv)], b)
            where
                update_ensure_eq seen (Var (Id n _)) s_ | n `notElem` seen =
                    let
                        s_' = updateStateFocusMap n 
                            $ s_ { non_red_path_conds = setFocus n Focused (expr_env s_) $ non_red_path_conds s_ }
                    in
                    case E.lookupConcOrSym n (expr_env s_') of
                        Just (E.Conc ec) -> update_ensure_eq (HS.insert n seen) ec s_'
                        _ -> s_'
                update_ensure_eq seen app@(App e1 e2) s_ | Data _:_ <- unApp app =
                    update_ensure_eq seen e1 (update_ensure_eq seen e2 s_)
                update_ensure_eq _ _ s_ = s_

        -- (2) Empty NRPCs
        red rv s@(State {  exec_stack = stck, non_red_path_conds = nrpc })
               b@(Bindings { name_gen = ng } )
            | currExprIsFalse s
            , Stck.null stck
            , allNRPC (\(NRPC focus _ _) -> isUnfocused focus) nrpc =
                let (empty_nrpc, ng') = emptyNRPC ng in
                return (Finished, [(s { non_red_path_conds = empty_nrpc }, rv)], b { name_gen = ng' } )
            where
                isUnfocused (Unfocused _) = True
                isUnfocused Focused = False

        -- Otherwise, do n othhing
        red rv s b =
            return (Finished, [(s, rv)], b)

verifySolveNRPC :: Monad m => Reducer m () VerifierTracker
verifySolveNRPC = mkSimpleReducer (const ()) red
    where
        red _
                        s@(State { expr_env = eenv
                                 , curr_expr = cexpr
                                 , exec_stack = stck
                                 , non_red_path_conds = nrs :<* nr@(NRPC focus nre1 nre2)
                                 , track = vt
                                 })
                                b
            
            | not (isNRPCSymFun eenv nr) || allNRPC (isNRPCSymFun eenv) nrs =
            let
                stck' = Stck.push (CurrExprFrame (EnsureEq nre2) cexpr) stck

                -- Inline variables at the center of the app. Required for soundness. Suppose the heap is:
                -- @ g = f ; f = symbolic Int -> Int @
                -- and we have a lone NRPC:
                -- @ g 1 = False @
                -- We must avoid removing @ g 1 @ from the NRPCs, reducing it to `f 1`, and then concluding that
                -- `f 1` is approximated by `g 1` (and so can be discarded)
                nre1' = inlineInner eenv nre1
                s' = s { curr_expr = CurrExpr Evaluate nre1'
                       , exec_stack = stck'
                       , non_red_path_conds = nrs
                       , focused = focus
                       , track = vt {tail_called_funcs = HS.empty } }

                in return (InProgress, [(s', ())], b)
            | otherwise = 
                let s' = s { non_red_path_conds = nr :*> nrs} in
                return (InProgress, [(s', ())], b)
        red _ s b = return (Finished, [(s, ())], b)

isNRPCSymFun :: ExprEnv -> NRPC -> Bool
isNRPCSymFun eenv (NRPC _ e1 _) = is_sym_fun HS.empty e1
    where
        is_sym_fun seen e
            | (Var (Id n _)):_ <- es
            , n `elem` seen = False
            | (Var (Id n _)):_ <- es
            , Just (E.Sym _) <- E.deepLookupConcOrSym n eenv = True
            | (Var (Id n _)):_ <- es
            , Just (E.Conc e_c) <- E.deepLookupConcOrSym n eenv = is_sym_fun (HS.insert n seen) e_c
            | otherwise = False
            where
                es = stripAllTicks $ unApp e

inlineInner :: ExprEnv -> Expr -> Expr
inlineInner eenv e
    | (Tick tick (Var (Id n t))):es <- unApp e
    , Just v <- E.deepLookupVar n eenv = mkApp (Tick tick (Var (Id v t)):es)
inlineInner _ e = e

verifyHigherOrderHandling :: MonadIO m => Reducer m () t
verifyHigherOrderHandling = mkSimpleReducer (const ()) red
    where
        red _ s@(State { curr_expr = CurrExpr _ ce
                       , expr_env = eenv
                       , type_env = tenv
                       , known_values = kv
                       , type_classes = tc 
                       , tyvar_env = tvnv }) b@(Bindings { name_gen = ng })
            | (App (Var (Id n raw_ty_fun)) ar) <- stripAllTicks ce
            , let ty_fun = tyVarSubst tvnv raw_ty_fun
            , E.isSymbolic n eenv =
                let
                    ty_ar = typeOf tvnv ar
                    (lam_x, ng2) = freshId ty_ar ng
                in
                case ty_fun of
                    TyFun (TyFun t1 t2) t3 ->
                        let
                            (pass, ng3) = freshId t1 ng2
                            (wrapper, ng4) = freshId (TyFun t2 t3) ng3
                            func_body = Lam TermL lam_x . App (Var wrapper) . App (Var lam_x) $ Var pass
                            eenv' = E.insertSymbolic wrapper
                                  . E.insertSymbolic pass
                                  $ E.insert n func_body eenv
                            
                            s' = s { curr_expr = CurrExpr Evaluate (App func_body ar), expr_env = eenv' }
                        in
                        return (InProgress, [(s', ())], b { name_gen = ng4 })
                    _ -> let
                            (bindee, ng3) = freshId ty_ar ng2
                            (ret_true, ng4) = freshId (case ty_fun of
                                                        TyFun _ t2 -> t2
                                                        _ -> error "verifyHigherOrderHandling: not tyfun") ng3
                            (ret_false, ng5) = freshId ty_fun ng4

                            eq_tc = case lookupTCDict tc (eqTC kv) ty_ar of
                                    Just tc -> tc
                                    Nothing -> error $ "verifyHigherOrderHandling: unsupported type" ++ "\n" ++ show ty_fun ++ "\n" ++ show ty_ar
                            eq_f = eqFunc kv
                            eq_f_i = Id eq_f (typeOf tvnv . fromJust $ E.lookup eq_f eenv)

                            e = mkApp [Var eq_f_i, Type ty_ar, Var eq_tc, Var lam_x, ar]

                            func_body =
                                Lam TermL lam_x $ 
                                    Case e bindee (returnType ty_fun)
                                        [ Alt (DataAlt (mkDCTrue kv tenv) []) (Var ret_true)
                                        , Alt (DataAlt (mkDCFalse kv tenv) []) (App (Var ret_false) (Var lam_x))]

                            eenv' = E.insertSymbolic ret_true
                                . E.insertSymbolic ret_false
                                $ E.insert n func_body eenv

                            s' = s { curr_expr = CurrExpr Evaluate (App func_body ar), expr_env = eenv'}
                        in
                        return (InProgress, [(s', ())], b {name_gen = ng5})
        red _ s b = return (Finished, [(s, ())], b)

unifyNRPCReducer :: Monad m =>
                    HS.HashSet Name -- ^ Names that should not be inlined (often: top level names from the original source code)
                 -> Reducer m () VerifierTracker
unifyNRPCReducer no_inline = mkSimpleReducer (const ()) red
    where
        red rv s@(State { expr_env = eenv, non_red_path_conds = nrpc, track = vt@VT { focus_map = fm } }) b =
            let
                (nrpc', fm', eenv') = unifyNRPCs no_inline eenv fm nrpc
                s' = s { expr_env = eenv'
                       , non_red_path_conds = nrpc'
                       , track = vt { focus_map = fm' } }
            in
            return (Finished, [(s', rv)], b)

-- | If two NRPCs have syntactically equal LHS and consistent (i.e. concretized to the same constructor(s)) RHS,
-- we can unify them. This makes it easier to find approximations because we have to match up fewer NRPCs. 
unifyNRPCs :: HS.HashSet Name
           -> ExprEnv
           -> FocusMap
           -> NonRedPathConds
           -> (NonRedPathConds, FocusMap, ExprEnv)
unifyNRPCs _ eenv fm nrpc@EmpNRPC = (nrpc, fm, eenv)
unifyNRPCs no_inline eenv fm (nrpc@(NRPC focus1 e1 v1) :*> nrpcs) =
    let
        con_nrpc = listToMaybe
                 $ mapMaybe (\(NRPC focus2 e2 v2) ->
                    case eqUpToTypesInline no_inline eenv (stripAllTicks e1) (stripAllTicks e2) of
                        True -> (, focus2) <$> alignVar HS.empty HS.empty eenv v1 v2
                        False -> Nothing)
                 $ toListNRPC nrpcs
    in
    case con_nrpc of
        Just (eenv', focus2) ->
            let
                (fm', nrpcs') = case (focus1, focus2) of
                                    (_, Focused) -> (fm, nrpcs)
                                    (Unfocused n1, Unfocused n2) -> (updateFocusMap n1 n2 fm, nrpcs)
                                    (Focused, Unfocused n) -> (fm, setFocus n Focused eenv nrpcs)
            in
            unifyNRPCs no_inline eenv' fm' nrpcs'
        Nothing -> mapFst3 (nrpc :*>) $ unifyNRPCs no_inline eenv fm nrpcs

alignVar :: HS.HashSet Name -> HS.HashSet Name -> ExprEnv -> Expr -> Expr -> Maybe ExprEnv
alignVar _ _ eenv (Var (Id n1 _)) v@(Var (Id n2 _))
    | n1 == n2 = Just eenv
alignVar _ _ eenv (Var (Id n1 _)) e2
    | E.isSymbolic n1 eenv = Just $ E.insert n1 e2 eenv
alignVar _ _ eenv e1 (Var (Id n2 _))
    | E.isSymbolic n2 eenv = Just $ E.insert n2 e1 eenv
alignVar seen1 seen2 eenv (Var (Id n1 _)) e2
    | not (n1 `elem` seen1)
    , Just e1 <- E.lookup n1 eenv = alignVar (HS.insert n1 seen1) seen2 eenv e1 e2
alignVar seen1 seen2 eenv e1 (Var (Id n2 _))
    | not (n2 `elem` seen2)
    , Just e2 <- E.lookup n2 eenv = alignVar seen1 (HS.insert n2 seen2) eenv e1 e2

alignVar _ _ eenv (Data d1) (Data d2) | dcName d1 == dcName d2 = Just eenv
alignVar seen1 seen2 eenv (App a1 a2) (App a1' a2') = do
    eenv' <- alignVar seen1 seen2 eenv a1 a1'
    alignVar seen1 seen2 eenv' a2 a2'

alignVar _ _ _ _ _ = Nothing

-- | Discard states with inconsistent NRPCs
inconsistentNRPCHalter :: Monad m =>
                          HS.HashSet Name -- ^ Names that should not be inlined (often: top level names from the original source code)
                       -> Halter m (HS.HashSet (Expr, Expr), Goal) r VerifierTracker
inconsistentNRPCHalter no_inline = 
    mkSimpleHalter (\_ -> (HS.empty, Theorem))
                   (\hv _ _ -> hv)
                   inc_check
                   add_nrpc
    where
        inc_check (hv, _) _ s@(State { expr_env = eenv })
            | currExprIsFalse s
            , not (checkNRPCConsistent no_inline eenv hv) = return (Discard "inconsistentNRPCHalter")
            | otherwise = return Continue
        
        add_nrpc (hv, g) _ _ s
            | not (g `isSameGoal` (goal . track $ s)) = (HS.empty, goal . track $ s)
            | currExprIsFalse s = foldl' (\(hv_, g) (NRPC _ e1 e2) -> (HS.insert (e1, e2) hv_, g)) (hv, g) (toListNRPC $ non_red_path_conds s)
            | otherwise = (hv, g)


-- | Check if all NRPCs are syntactically consistent.  Two NRPCs are INconsistent if they:
-- (1) have syntactically equal (after some inlining) LHS
-- (2) have different constructors on the RHS
--
-- For example, if we have:
-- @ f x y (1:xs) = a:as
--   f x y (1:xs) = []
-- @
-- clearly these NRPCs are inconsistent because it is not possible that the pure `f` function
-- returns both a cons and an empty list.
checkNRPCConsistent :: HS.HashSet Name
                    -> ExprEnv
                    -> HS.HashSet (Expr, Expr)
                    -> Bool
checkNRPCConsistent no_inline eenv = snd . foldl' incCheck ([], True)
    where
        incCheck (prev, b) (e1, e2) =
            let
                b' = any (\(p1, p2) -> eqUpToTypesInline no_inline eenv (stripAllTicks e1) (stripAllTicks p1)
                                    && diffConstr (center HS.empty e2) (center HS.empty p2)) prev
            in
            ((e1, e2):prev, b && not b')

        center seen v@(Var (Id n _))
            | HS.member n seen = v
            | Just e <- E.lookup n eenv = center (HS.insert n seen) e
        center seen e
            | v@(Var _):_ <- unApp e = center seen v
        center _ e = e

        diffConstr e1 e2
            | Data d1:_ <- unApp e1
            , Data d2:_ <- unApp e2 = dc_name d1 /= dc_name d2
        diffConstr _ _ = False

-- | If a state S has a current expression, path constraints, and NRPC set that are approximated by some
-- other state S', discard S. Any counterexample discoverable from S is also discoverable from S'.
approximationHalter :: (Solver solver, SM.MonadState (ApproxPrevs VerifierTracker) m, MonadIO m) =>
                       solver
                    -> HS.HashSet Name -- ^ Names that should not be inlined (often: top level names from the original source code)
                    -> Halter m () r VerifierTracker
approximationHalter = approximationHalter' (\_ old_state new_state -> goal (track old_state) `isValidFor` goal (track new_state))

-- | Discard all other states if we find a counterexample.
discardOnFalse :: Monad m => Halter m () (ExecRes VerifierTracker) VerifierTracker
discardOnFalse = (mkSimpleHalter (\_ -> ())
                                (\hv _ _ -> hv)
                                (\_ _ _ -> return Continue)
                                (\hv _ _ _ -> hv))
                    { discardOnStart = \_ pr s -> discard s pr
                    , filterAllStates = filterAll }
    where
        discard curr_state (Processed { accepted = acc }) = any checkShouldDiscard acc
            where
                checkShouldDiscard (ExecRes { final_state = prev_s })
                    | currExprIsFalse prev_s = goal (track prev_s) `isSameGoal` goal (track curr_state) 
                    | otherwise = False
        
        -- Continue running if we have any states left trying to prove the main theorem.
        -- Otherwise, drop all states.
        filterAll all_states | any (isTheorem . goal . track . exStateToState). concat . M.elems $ all_states = all_states
                             | otherwise = M.empty

currExprIsBool :: Bool -> State t -> Bool
currExprIsBool b s = E.deepLookupExpr (getExpr s) (expr_env s) == mkBool (known_values s) b

currExprIsFalse :: State t -> Bool
currExprIsFalse = currExprIsBool False

currExprIsTrue :: State t -> Bool
currExprIsTrue = currExprIsBool False

-------------------------------------------------------------------------------
-- Lemmas
-------------------------------------------------------------------------------

data LemmaInfo = LI { generated_lem :: [VerifierState] -- ^ Previously generated potential lemmas
                    , discarded_lem :: [VerifierState] -- ^ Lemmas proven to be false
                    }

emptyLemmaInfo :: LemmaInfo
emptyLemmaInfo = LI { generated_lem = [], discarded_lem = [] }

addGenerated :: [VerifierState] -> LemmaInfo -> LemmaInfo
addGenerated new_lem lem_info@(LI { generated_lem = gen }) = lem_info { generated_lem = new_lem ++ gen }

addDiscarded :: [VerifierState] -> LemmaInfo -> LemmaInfo
addDiscarded new_dis lem_info@(LI { discarded_lem = dis }) = lem_info { discarded_lem = new_dis ++ dis }

genLemmaReducer :: (MonadIO m, SM.MonadState LemmaInfo m,  Solver solver) => HS.HashSet Name -> solver -> Reducer m () VerifierTracker
genLemmaReducer no_inline solver = (mkSimpleReducer (const ()) red) { onDiscard = dis }
    where
        red rv s b
            | CurrExpr Return (Data (DataCon { dc_name = d })) <- curr_expr s
            , d == dc_name (mkDCFalse (known_values s) (type_env s)) = do
                lem_info <- SM.get
                (b', m_lem_s) <- mapAccumM (genLemmaState no_inline solver lem_info s) b (toListNRPC $ non_red_path_conds s)
                let lem_s = catMaybes m_lem_s
                    lem_info' = addGenerated lem_s lem_info
                SM.put lem_info'
                return (NoProgress, (s, rv):map (,rv) lem_s, b')
            | otherwise = return (NoProgress, [(s, rv)], b)
        
        dis _ _ (State { track = VT { goal = Lemma _ lem_s } }) _ = do
            lem_info <- SM.get
            SM.put $ addDiscarded [lem_s] lem_info
        dis _ _ _ _ = return ()
   
genLemmaState :: (MonadIO m, Solver solver) => HS.HashSet Name -> solver -> LemmaInfo -> VerifierState -> Bindings -> NRPC -> m (Bindings, Maybe VerifierState)
genLemmaState no_inline solver (LI { generated_lem = gen_lems, discarded_lem = dis_lems }) s@(State { expr_env = eenv, known_values = kv }) b nrpc = do
    let (lemma_name, ng2) = freshSeededString "lemma" (name_gen b)
        (emp_nrpc, ng3) = emptyNRPC ng2
        (ng4, nrpcs) = addExistingNRPC ng3 (nrpc { nrpc_focus = Focused }) emp_nrpc

        lem_s = s { curr_expr = CurrExpr Evaluate (mkFalse kv)
                  , exec_stack = Stck.empty
                  , non_red_path_conds = nrpcs
                  , track = (track s) { tail_called_funcs = HS.empty, goal = Lemma lemma_name lem_s }}
    
    let mr_cont = mrContIgnoreNRPCTicks Nothing lookupConcOrSymState
        res_check = moreRestrictiveIncludingPCAndNRPC
                                                        solver
                                                        mr_cont
                                                        Nothing
                                                        lookupConcOrSymState
                                                        no_inline
    equiv_lemma <-liftIO $ findM (\prev -> liftM2 (&&) (res_check prev lem_s) (res_check lem_s prev)) gen_lems
    dis_lemma <-liftIO $ findM (\s -> res_check s lem_s) dis_lems

    -- No point in generating a lemma where the RHS is symbolic, as this would be trivially false
    let non_sym_rhs = case nrpc_rhs $ nrpc of
                        Var (Id n _) | Just (E.Conc _) <- E.deepLookupConcOrSym n eenv -> True
                        _ -> False

    case (non_sym_rhs, equiv_lemma, dis_lemma) of
        (True, Nothing, Nothing) -> do
            let pretty_nrpc = inlinePretty eenv nrpc
            liftIO . putStrLn $ "Try to prove "
                            <> (T.unpack . printHaskellDirty $ nrpc_lhs pretty_nrpc)
                            <> " = "
                            <> (T.unpack . printHaskellDirty $ nrpc_rhs pretty_nrpc)
            return ( b { name_gen = ng4 }, Just lem_s )
        _ -> return ( b { name_gen = ng4 }, Nothing )

mrContIgnoreNRPCTicks :: Maybe (GenerateLemma t l)
                      -> Lookup t
                      -> State t
                      -> State t
                      -> HS.HashSet Name
                      -> (HM.HashMap Id Expr, HS.HashSet (Expr, Expr))
                      -> Bool -- ^ indicates whether this is part of the "active expression"
                      -> [(Name, Expr)] -- ^ variables inlined previously on the LHS
                      -> [(Name, Expr)] -- ^ variables inlined previously on the RHS
                      -> Expr
                      -> Expr
                      -> Either [l] (HM.HashMap Id Expr, HS.HashSet (Expr, Expr))
mrContIgnoreNRPCTicks genLemma lkp s1 s2 ns hm active n1 n2 e1 e2 =
    case (e1, e2) of
        (Tick t1 e1', _) ->
            moreRestrictive' (mrContIgnoreNRPCTicks genLemma lkp) genLemma lkp s1 s2 ns hm active n1 n2 e1' e2
        (_, Tick t2 e2') ->
            moreRestrictive' (mrContIgnoreNRPCTicks genLemma lkp) genLemma lkp s1 s2 ns hm active n1 n2 e1 e2'
        _ -> Left []

acceptLemmaReducer :: (MonadIO m, SM.MonadState (ApproxPrevs VerifierTracker) m) => Reducer m () VerifierTracker
acceptLemmaReducer = (mkSimpleReducer (const ()) (\rv s b -> return (NoProgress, [(s, rv)], b))) { onDiscard = dis }
    where
        dis _ all_states s _
            | not . any (isSameGoal (goal $ track s) . goal . track . exStateToState) . concat . M.elems $ all_states
            , Lemma _ lem_s <- goal $ track s = do
                liftIO $ putStrLn ("adding\n" ++ T.unpack (prettyNonRedPaths (mkPrettyGuide ()) (non_red_path_conds $ inlineNRPC lem_s)))
                addApproxPrevs (lem_s { track = (track lem_s) { goal = Proven } })
            | otherwise = return ()

-------------------------------------------------------------------------------
-- Verifier Tracker
-------------------------------------------------------------------------------
type VerifierState = State VerifierTracker

data Goal = Theorem -- ^ The state is for the main theorem/property we are trying to prove
          | Lemma Name VerifierState -- ^ The state is for a helper lemma we are trying to prove
          | Proven -- ^ The state corresponds to a property that has been proven correct
            deriving (Show, Read)

isTheorem :: Goal -> Bool
isTheorem Theorem = True
isTheorem _ = False

-- | `evidence isValidFor objective` checks if `evidence` can be used to discharge objective
isValidFor :: Goal -> Goal -> Bool
Theorem `isValidFor` Theorem = True
Lemma n1 _ `isValidFor` Lemma n2 _ = n1 == n2
Proven `isValidFor` _ = True
_ `isValidFor` _ = False

-- | `evidence isSameGoal objective` checks if both Goals are for the theorem, both for the same lemma, or both proven
isSameGoal :: Goal -> Goal -> Bool
Theorem `isSameGoal` Theorem = True
Lemma n1 _ `isSameGoal` Lemma n2 _ = n1 == n2
Proven `isSameGoal` Proven = True
_ `isSameGoal` _ = False

data VerifierTracker = VT { goal :: Goal
                          , tail_called_funcs :: TailCalls -- ^ Functions called while in tail position 
                          , focus_map :: FocusMap }
                          deriving (Show, Read)
type TailCalls = HS.HashSet Name
type FocusMap = HM.HashMap Name (HS.HashSet Name)

initVerifierTracker :: VerifierTracker
initVerifierTracker = VT { goal = Theorem, tail_called_funcs = HS.empty, focus_map = HM.empty }

updateStateFocusMap :: Name -> VerifierState -> VerifierState
updateStateFocusMap n s@(State { focused = Unfocused n'
                               , track = vt@VT { focus_map = fm } }) =
            let
                fm' = updateFocusMap n' n fm
            in
            s { track = vt { focus_map = fm' } }
updateStateFocusMap _ s = s

-- | When Name1 is switched to focused, Name2 should also then be switched to focused
updateFocusMap :: Name -- Name1
               -> Name -- Name2
               -> FocusMap
               -> FocusMap
updateFocusMap n1 n2 = HM.insertWith HS.union n1 (HS.fromList [n2])

prettyVerifierTracker :: PrettyGuide -> VerifierTracker -> T.Text
prettyVerifierTracker pg (VT { focus_map = fm, tail_called_funcs = tcf, goal = g}) =
    "Goal:\n"
    <> prettyGoal g
    <> "\nFocus:\n" <>
    (T.intercalate "\n" . map pretty_fm $ HM.toList fm)
    <> "\nTail called funcs:\n" <>
    (T.intercalate "\n" . map (printName pg) $ HS.toList tcf)
    where
        pretty_fm (k, v) = printName pg k <> " -> " <> T.intercalate ", " (map (printName pg) $ HS.toList v)

        prettyGoal Theorem = "Theorem"
        prettyGoal (Lemma n _) = "Lemma " <> printName pg n
        prettyGoal Proven = "Proven"

instance ASTContainer VerifierTracker Expr where
    containedASTs _ = []
    modifyContainedASTs _ vt = vt

instance ASTContainer VerifierTracker Type where
    containedASTs _ = []
    modifyContainedASTs _ vt = vt

instance Named VerifierTracker where
    names vt = names (goal vt) <> names (focus_map vt)
    rename old new vt = VT { goal = rename old new (goal vt), tail_called_funcs = rename old new (tail_called_funcs vt), focus_map = rename old new (focus_map vt) }
    renames hm vt = VT { goal = renames hm (goal vt), tail_called_funcs = renames hm (tail_called_funcs vt), focus_map = renames hm (focus_map vt) }

instance Named Goal where
    names Theorem = mempty
    names (Lemma n _) = Seq.singleton n
    names Proven = mempty

    rename _ _ Theorem = Theorem
    rename old new (Lemma n s) = Lemma (rename old new n) s
    rename _ _ Proven = Proven

    renames _ Theorem = Theorem
    renames hm (Lemma n s) = Lemma (renames hm n) s
    renames _ Proven = Proven
