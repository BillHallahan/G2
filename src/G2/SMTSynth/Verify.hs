{-# LANGUAGE OverloadedStrings, TupleSections #-}

module G2.SMTSynth.Verify ( checkEquiv
                          , insertFCTick ) where

import G2.Config
import G2.Initialization.MkCurrExpr
import G2.Interface
import qualified G2.Initialization.Types as IT
import G2.Language
import qualified G2.Language.ExprEnv as E
import G2.Language.KnownValues as KV
import G2.Language.TyVarEnv as TV

import Control.Monad.IO.Class
import qualified Data.Foldable as F
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import Data.Maybe
import qualified Data.Text as T

checkEquiv :: Config -> HM.HashMap Name Id -> SimpleState -> Name -> String -> IO ()
checkEquiv func_config equiv_annots simp_state entry_real entry_smt
    | Just (entry_real_name, real_e) <- E.lookupNameMod (nameOcc entry_real) (nameModule entry_real) (IT.expr_env simp_state)
    , Just (entry_smt_name, _) <- E.lookupNameMod (T.pack entry_smt) (nameModule entry_real) (IT.expr_env simp_state)
    , Just (comp_name, comp_e) <- E.lookupNameMod "comp" (Just "G2.Plugin") (IT.expr_env simp_state) = do
        -- Get a Config to run this specific function
        let func_config' = func_config { step_limit = False
                                       , smt_strings = UseSMTStrings
                                       , smt_prim_lists = UseSMTSeq { add_to_dcs = True, add_to_funcs = True }
                                       , smt_strings_strictness = StrictSMTStrings
                                       , search_strat = Subpath
                                       , min_found = 1 }

        let entry_id = Id entry_real_name $ typeOf TV.empty real_e
            (init_state, bindings) = initStateFromSimpleState simp_state [nameModule entry_real] False
                                (mkCurrExpr TV.empty Nothing Nothing entry_id)
                                (E.higherOrderExprs TV.empty . IT.expr_env)
                                func_config'
            bindings' = bindings { higher_order_inst = HS.empty }

            eenv = expr_env init_state
            kv = known_values init_state
            tv_env = tyvar_env init_state

            real_var = Var (Id entry_real_name $ typeOf tv_env real_e)
            smt_var = Var (Id entry_smt_name $ typeOf tv_env real_e)

            -- Modify the real function to replace recursive calls with calls to the SMT definitions
            real_e_mod_def = case E.lookup entry_real_name eenv of
                                    Just e -> e
                                    Nothing -> error "checkEquiv: definition not found"
            real_e' = replaceVars equiv_annots real_e_mod_def
            eenv' = E.insert entry_real_name real_e' eenv
            eenv'' = insertFCTickForAll (HM.toList $ HM.map idName equiv_annots) eenv' tv_env
        
            -- Set up a call to compare the real and SMT definitions
            in_vars = mapMaybe (flip E.lookup eenv'') $ input_names bindings'
            call_real = mkApp (real_var:in_vars)
            call_smt = mkApp (smt_var:in_vars)
            eq = fromMaybe (error $ "checkEquiv: could not generate Eq typeclass")
               $ typeClassInst (type_classes init_state) HM.empty (KV.eqTC kv) (typeOf tv_env call_real)

            comp_expr = mkApp [ Var (Id comp_name $ typeOf tv_env comp_e)
                              , Type TyUnknown
                              , eq
                              , call_real
                              , call_smt]
            comp_state = init_state { expr_env = eenv''
                                    , curr_expr = CurrExpr Evaluate comp_expr
                                    , true_assert = False }
            config_no_output = func_config' { print_output = False }
        (ers, _, _, time_outs, _) <- liftIO $ runG2WithConfig
                                                            [] [] entry_id "" []
                                                            [nameModule entry_real_name]
                                                            comp_state
                                                            config_no_output
                                                            bindings'
        
        -- Get States corresponding to SMT calls from the states that violated the spec.
        -- Consider some functions:
        --      {-# ANN corr (SMTEquivIs "smtCorr") #-}
        --      corr :: Int -> Int
        --      corr = incorr

        --      smtCorr :: Int -> Int
        --      smtCorr x = x + 1

        --      {-# ANN incorr (SMTEquivIs "smtIncorr") #-}
        --      incorr :: Int -> Int
        --      incorr x = x + 1

        --      smtIncorr :: Int -> Int
        --      smtIncorr x = x + 2
        -- If we run corr, we may get a "counterexample" that corr 0 = 2. However, the glitch here is actually that
        -- the specification of incorr is wrong. We figure this out by logging all values passed into and returned from
        -- SMT definitions, and then checking if those values actually conform to the behavior of the real function.

        let smt_call_xs = (checkFCStateBindings eenv) ers bindings'
        mapM_ (\(func_n, new_s, new_b) -> do
            runG2WithConfig [] [] (Id func_n TyUnknown) "" [] [nameModule entry_real_name] new_s func_config' new_b) smt_call_xs

        case ers of
            [] | NoTimeOut <- time_outs -> putStrLn $ "Equivalent: "
                                    <> T.unpack (nameOcc entry_real_name) <> " and "
                                    <> T.unpack (nameOcc entry_smt_name)
            _ | TimedOut _ <- time_outs -> putStrLn $ "Time Out: "
                                                <> T.unpack (nameOcc entry_real_name) <> " and "
                                                <> T.unpack (nameOcc entry_smt_name)
            _ -> putStrLn $ "Equivalence not proven: "
                                    <> T.unpack (nameOcc entry_real_name) <> " and "
                                    <> T.unpack (nameOcc entry_smt_name)

        return ()
    | otherwise = do
        putStrLn "checkEquiv: functions not found"
        return ()

replaceVars :: HM.HashMap Name Id -> Expr -> Expr
replaceVars m = modify go
    where
        go (Var (Id n _)) | Just i <- HM.lookup n m = Var i
        go e = e

insertFCTickForAll :: [(Name, Name)] -> ExprEnv -> TyVarEnv -> ExprEnv
insertFCTickForAll ns eenv tv_env =
    F.foldl' (\eenv_ (real_n, smt_n) -> case E.lookup smt_n eenv_ of
                            Just e -> E.insert smt_n (insertFCTick e real_n tv_env) eenv_
                            Nothing -> eenv_) eenv ns

insertFCTick :: Expr -> Name -> TyVarEnv -> Expr
insertFCTick expr func tv_env =
    let ret_name = Name "G2_!!_RET_VAR" Nothing 0 Nothing in
    insertInLams (\is e ->
                    let
                        ty_e = typeOf tv_env e
                        anon_ty = anonArgumentTypes ty_e
                        new_lam_is = zipWith (\i at -> Id (Name "G2_!!_LAM" Nothing i Nothing) at) [1..] anon_ty
                        ret_id = Id ret_name (returnType ty_e)

                        all_is = is ++ new_lam_is
                        e' = mkApp $ e:map Var new_lam_is
                    in
                       mkLams (map (TermL,) new_lam_is)
                    $ Let [(ret_id, e')] $ Tick (FCTick $ FuncCall { funcName = func, arguments = map Var all_is, returns = Var ret_id }) (Var ret_id)) expr

checkFCStateBindings :: ExprEnv -> [ExecRes ()] -> Bindings -> [(Name, State (), Bindings)]
checkFCStateBindings orig_eenv er bindings =     
    let new_state_bindings =
            concatMap (\ExecRes { final_state = s@State { expr_env = eenv, tyvar_env = tv_env, known_values = kv, type_classes = tc } } ->
                map (\fc->
                        let
                            func_t = typeOf tv_env $ fromMaybe (error "runFunc: func not found") $ E.lookup (funcName fc) eenv
                            num_ty = length $ leadingTyForAllBindings func_t

                            (arg_ns, ng') = freshIds (map (typeOf tv_env) $ arguments fc) (name_gen bindings)
                            ty_args_ns = take num_ty arg_ns
                            var_args_ns = drop num_ty arg_ns

                            tv_env' = foldr (\(Id n _, e) -> TV.insert n (fromMaybe TyBottom $ TV.deepLookup tv_env e)) tv_env (zip ty_args_ns $ arguments fc)
                            
                            -- Set up the expression environment. We want function definitions from the ORIGINAL expression environment,
                            -- but also all bindings from the new expression environment.
                            -- We also introduce bindings for the arguments that we are running the function on.
                            eenv' = orig_eenv `E.union` eenv
                            eenv'' = foldr (\(Id n _, e) -> E.insert n e) eenv' (zip var_args_ns . drop num_ty $ arguments fc)

                            -- Set up the current expression
                            apply_to_args = mkApp $ Var (Id (funcName fc) TyUnknown):map Var arg_ns
                            ret_val = returns fc
                            t = typeOf tv_env ret_val

                            eq_func = Var (Id (eqFunc kv) TyUnknown)
                            eq_dict = fromMaybe (error $ "checkEquiv: could not generate Eq typeclass" ++ "\n" ++ show (typeOf tv_env t) ++ "\n" ++ show t ++ "\n" ++ show ret_val)
                                    $ typeClassInst  tc HM.empty (KV.eqTC kv) t
                            
                            call_res_i = Id (Name "CALL_!!_RES_G2__" Nothing 0 Nothing) t
                            call_res_v = Var call_res_i
                            eq_call = mkApp [ eq_func
                                            , Type t
                                            , eq_dict
                                            , call_res_v
                                            , ret_val
                                            ]
                            assert_eq = Assert Nothing eq_call call_res_v
                            let_e = Let [(call_res_i, apply_to_args)] assert_eq
                        in
                        ( funcName fc
                        , s { expr_env = eenv'', tyvar_env = tv_env', true_assert = False, curr_expr = CurrExpr Evaluate let_e }
                        , bindings { input_names = map idName arg_ns, name_gen = ng' })
                    ) (reached_fc_ticks s)
            ) er
    in new_state_bindings
