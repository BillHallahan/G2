{-# LANGUAGE FlexibleContexts, MultiParamTypeClasses, MultiWayIf, OverloadedStrings #-}

module G2.Verify.Reducer ( VerifierTracker
                         , initVerifierTracker
                         , prettyVerifierTracker
                         
                         , nrpcAnyCallReducer
                         , adjustFocusReducer
                         , verifySolveNRPC
                         , verifyHigherOrderHandling
                         , approximationHalter
                         
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
import G2.Language.KnownValues
import qualified G2.Language.Stack as Stck
import qualified G2.Language.Typing as T
import G2.Lib.Printers
import G2.Solver
import G2.Verify.Config

import Control.Monad.IO.Class
import qualified Control.Monad.State as SM
import qualified Data.HashSet as HS
import qualified Data.HashMap.Strict as HM
import Data.List
import Data.Maybe
import Data.Sequence

import qualified Data.Text as T


-- | When a newly reached function application is approximated by a previously seen (and thus explored) function application,
-- shift the new function application into the NRPCs.
nrpcAnyCallReducer :: MonadIO m =>
                      HS.HashSet Name -- ^ Names of functions that should not be approximated
                   -> VerifyConfig
                   -> Config
                   -> Reducer m Int t
nrpcAnyCallReducer no_nrpc_names v_config config =
    (mkSimpleReducer (const 0) red)
            { onAccept = \s b nrpc_count -> do
            if print_num_nrpc config
                then liftIO . putStrLn $ "NRPCs Generated: " ++ show nrpc_count
                else return ()
            return (s, b) }

    where        
        red rv s@(State { curr_expr = CurrExpr _ ce, expr_env = eenv, tyvar_env = tvnv }) b@(Bindings { name_gen = ng })
            | maybe True (allowed_frame . fst) (Stck.pop (exec_stack s))
            
            , let wrapped_ce = applyWrap (getExpr s) (exec_stack s)
            , let stripped_ce = stripNRBT wrapped_ce
            , v@(Var (Id _ _)):es@(_:_) <- unApp stripped_ce  = do

                -- Convert arguments into NRPCs
                let (s', ng') = if (arg_rev_abs v_config) == AbsFuncArgs then argsToNRPCs s (name_gen b) v es else (s, ng)

                -- Given a function call `f x1 ... xn`, we move the entire call to `f` into an NRPC.
                -- Note that createNewCond wraps the function call with a Tick.
                -- This prevents that same function call from being immediately turned back into an NRPC
                -- when it is removed from the NRPCs.
                let e = applyWrap (getExpr s) (exec_stack s)
                    nr_s_ng = if
                                -- Line (*) make sure we don't add back to NRPCs immediately.
                                | not (hasNRBT wrapped_ce) -- (*)
                                , allowedApp e eenv tvnv -> createNonRed ng' (focused s') s'
                                | otherwise -> Nothing
                
                case nr_s_ng of
                    Just (nr_s, _, _, ng'') -> return (Finished, [(nr_s, rv + 1)], b { name_gen = ng'' })
                    _ -> return (Finished, [(s', rv)], b { name_gen = ng' })
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
                not (n' `HS.member` no_nrpc_names) && not (E.isSymbolic n' eenv)
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
                ((s', ng'), es') = mapAccumR (\(s_, ng_) e_ ->
                                                let
                                                    (e_', s_', ng_') = argsToNRPCs' s_ ng_ HS.empty e_
                                                in
                                                ((s_', ng_'), e_')) (s, ng) es
            in
            (s' { curr_expr = CurrExpr Evaluate . mkApp $ v:es' }, ng')
        
        argsToNRPCs' s@(State { expr_env = eenv }) ng grace v@(Var (Id n _))
            | Just (E.Conc e) <- E.lookupConcOrSym n eenv =
                let
                    (e', s', ng') = argsToNRPCs' s ng grace e
                    eenv' = E.insert n e' (expr_env s')
                in
                (v, s' { expr_env = eenv' }, ng')
        argsToNRPCs' s@(State { expr_env = eenv, tyvar_env = tvnv }) ng grace e@(App _ _)
            | allowedApp e eenv tvnv
            , v:es <- unApp e =
                let
                    arg_holes = holes es
                    grace' = case v of
                                Data _ -> grace
                                _ -> HS.empty 
                    ((s', ng'), es') = mapAccumR
                        (\(s_, ng_) (e_, other_es) -> appArgToNRPC s_ ng_ grace' e_ other_es) (s, ng) arg_holes
                    e' = mkApp (v:es')
                in
                case createNonRed' ng' (Unfocused ()) s' e' of
                    Just (s'', sym_i, _, ng'') -> (Var sym_i, s'', ng'')
                    Nothing -> (e', s', ng')
        argsToNRPCs' s ng _ e = (e, s, ng)

        -- (Maybe) converts an argument of an application into an NRPC.
        -- `e` is the argument to possible convert, `es` is all other arguments.
        -- See Note [Replacing nested function applications]- we replace `e` only if
        -- some symbolic variable in `e` also occurs in some other argument in `e`.
        -- The `grace` variable is used to replace arguments through data constructors,
        -- see Note [Data Constructor Arguments to NRPCs]
        appArgToNRPC s@(State { expr_env = eenv }) ng grace e other_es
            | let e_symb = symbolic_names eenv e
            , let es_symb = HS.unions (grace:map (symbolic_names eenv) other_es)
            , (not . HS.null $ e_symb `HS.intersection` es_symb) || shared_var_heuristic v_config == NoSharedVarHeuristic = 
                let (e_', s_', ng_') = argsToNRPCs' s ng es_symb e in
                ((s_', ng_'), e_')
            | otherwise = ((s, ng), e)

        symbolic_names eenv (Var (Id n _))
            | Just (E.Sym _) <- E.lookupConcOrSym n eenv = HS.singleton n
            | Just (E.Conc e) <- E.lookupConcOrSym n eenv = symbolic_names eenv e
        symbolic_names eenv (App e1 e2) = symbolic_names eenv e1 `HS.union` symbolic_names eenv e2
        symbolic_names _ _ = HS.empty

        allowed_frame (ApplyFrame _) = False
        allowed_frame _ = True

        applyWrap e stck | Just (ApplyFrame a, stck') <- Stck.pop stck = applyWrap (App e a) stck'
                         | otherwise = e
        
        stripNRBT (Tick nl e) | isNonRedBlockerTick nl = e
        stripNRBT (App e1 e2) = App (stripNRBT e1) e2
        stripNRBT e = e

        hasNRBT (Tick nl e) | isNonRedBlockerTick nl = True
                            | otherwise = hasNRBT e
        hasNRBT (App e1 _) = hasNRBT e1
        hasNRBT _ = False

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
                s' = updateFocusMap n s
            in
            return (Finished, [(s', rv)], b)
        red rv s@(State { curr_expr = CurrExpr _ e, exec_stack = stck, focused = Focused }) b
            | Just (CurrExprFrame (EnsureEq _) _, _) <- Stck.pop stck =
                let s' = update_ensure_eq e s in
                return (Finished, [(s', rv)], b)
            where
                update_ensure_eq (Var (Id n _)) s_ =
                    let
                        s_' = updateFocusMap n 
                            $ s_ { non_red_path_conds = setFocus n Focused (expr_env s_) $ non_red_path_conds s_ }
                    in
                    case E.lookupConcOrSym n (expr_env s_') of
                        Just (E.Conc ec) -> update_ensure_eq ec s_'
                        _ -> s_'
                update_ensure_eq app@(App e1 e2) s_ | Data _:_ <- unApp app =
                    update_ensure_eq e1 (update_ensure_eq e2 s_)
                update_ensure_eq _ s_ = s_

        -- (2) Empty NRPCs
        red rv s@(State {  exec_stack = stck, non_red_path_conds = nrpc })
               b@(Bindings { name_gen = ng } )
            | currExprIsFalse s
            , Stck.null stck
            , allNRPC (\(focus, _, _) -> isUnfocused focus) nrpc =
                let (empty_nrpc, ng') = emptyNRPC ng in
                return (Finished, [(s { non_red_path_conds = empty_nrpc }, rv)], b { name_gen = ng' } )
            where
                isUnfocused (Unfocused _) = True
                isUnfocused Focused = False

        -- Otherwise, do n othhing
        red rv s b =
            return (Finished, [(s, rv)], b)

verifySolveNRPC :: Monad m => Reducer m () t
verifySolveNRPC = mkSimpleReducer (const ()) red
    where
        red _
                        s@(State {curr_expr = cexpr
                                , exec_stack = stck
                                , non_red_path_conds = nrs :<* (focus, nre1, nre2)
                                })
                                b@(Bindings { name_gen = ng }) =
            
            let
                stck' = Stck.push (CurrExprFrame (EnsureEq nre2) cexpr) stck
                s' = s { curr_expr = CurrExpr Evaluate nre1
                       , exec_stack = stck'
                       , non_red_path_conds = nrs
                       , focused = focus }

                in return (InProgress, [(s', ())], b { name_gen = ng })
        red _ s b = return (Finished, [(s, ())], b)

verifyHigherOrderHandling :: MonadIO m => Reducer m () t
verifyHigherOrderHandling = mkSimpleReducer (const ()) red
    where
        red _ s@(State { curr_expr = CurrExpr _ ce
                       , expr_env = eenv
                       , type_env = tenv
                       , known_values = kv
                       , type_classes = tc 
                       , tyvar_env = tvnv }) b@(Bindings { name_gen = ng })
            | (App (Var (Id n ty_fun)) ar) <- ce
            , E.isSymbolic n eenv =
                let
                    ty_ar = typeOf tvnv ar
                    (lam_x, ng2) = freshId ty_ar ng
                    (bindee, ng3) = freshId ty_ar ng2

                    (ret_true, ng4) = freshId (returnType ty_fun) ng3
                    (ret_false, ng5) = freshId ty_fun ng4

                    eq_tc = case lookupTCDict tc (eqTC kv) ty_ar of
                                Just tc -> tc
                                Nothing -> error "verifyHigherOrderHandling: unsuported type"
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


-- | If a state S has a current expression, path constraints, and NRPC set that are approximated by some
-- other state S', discard S. Any counterexample discoverable from S is also discoverable from S'.
approximationHalter :: (Named t, Solver solver, SM.MonadState (ApproxPrevs t) m, MonadIO m) =>
                       solver
                    -> HS.HashSet Name -- ^ Names that should not be inlined (often: top level names from the original source code)
                    -> Halter m () r t
approximationHalter = approximationHalter' (\_ _ -> True)

-- | Discard all other states if we find a counterexample.
discardOnFalse :: Monad m => Halter m () (ExecRes t) t
discardOnFalse = (mkSimpleHalter (\_ -> ())
                                (\hv _ _ -> hv)
                                (\_ _ _ -> return Continue)
                                (\hv _ _ _ -> hv))
                    { discardOnStart = \_ pr s -> discard s pr }
    where
        discard (State { expr_env = eenv, known_values = kv }) (Processed { accepted = acc })
            = any (currExprIsFalse . final_state) acc

currExprIsBool :: Bool -> State t -> Bool
currExprIsBool b s = E.deepLookupExpr (getExpr s) (expr_env s) == mkBool (known_values s) b

currExprIsFalse :: State t -> Bool
currExprIsFalse = currExprIsBool False

currExprIsTrue :: State t -> Bool
currExprIsTrue = currExprIsBool False

-------------------------------------------------------------------------------
type VerifierState = State VerifierTracker

newtype VerifierTracker = VT { focus_map :: FocusMap }
                          deriving (Show, Read)

type FocusMap = HM.HashMap Name (HS.HashSet Name)

initVerifierTracker :: VerifierTracker
initVerifierTracker = VT { focus_map =HM.empty }

updateFocusMap :: Name -> VerifierState -> VerifierState
updateFocusMap n s@(State { focused = Unfocused n'
                          , track = VT { focus_map = fm } }) =
            let
                fm' = HM.insertWith HS.union n' (HS.fromList [n]) fm
            in
            s { track = VT { focus_map = fm' } }
updateFocusMap _ s = s

prettyVerifierTracker :: PrettyGuide -> VerifierTracker -> T.Text
prettyVerifierTracker pg (VT { focus_map = fm }) =
    T.intercalate "\n" . map pretty_fm $ HM.toList fm
    where
        pretty_fm (k, v) = printName pg k <> " -> " <> T.intercalate ", " (map (printName pg) $ HS.toList v)

instance ASTContainer VerifierTracker Expr where
    containedASTs _ = []
    modifyContainedASTs _ vt = vt

instance ASTContainer VerifierTracker Type where
    containedASTs _ = []
    modifyContainedASTs _ vt = vt

instance Named VerifierTracker where
    names vt = names (focus_map vt)
    rename old new vt = VT { focus_map = rename old new (focus_map vt) }
    renames hm vt = VT { focus_map = renames hm (focus_map vt) }