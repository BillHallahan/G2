{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module G2.Liquid.Interface ( LiquidData (..)
                           , LiquidReadyState
                           , lr_state
                           , lr_binding
                           , lrsMeasures
                           , Abstracted (..)
                           , AbstractedInfo (..)
                           , findCounterExamples
                           , runLHG2
                           , runLHCore
                           , liquidStateWithCall
                           , liquidStateWithCall'
                           , liquidStateFromSimpleStateWithCall
                           , liquidStateFromSimpleStateWithCall'
                           , liquidStateFromSimpleState

                           , cleanReadyState
                           , fromLiquidNoCleaning
                           , createLiquidReadyState
                           , processLiquidReadyState
                           , processLiquidReadyStateWithCall
                           , extractWithoutSpecs

                           , processLiquidReadyStateCleaning

                           , reqNames

                           , lhStateToCE
                           , printLHOut
                           , printCE) where

import G2.Config.Config

import G2.Translation
import G2.Interface
import G2.Language as Lang
import G2.Language.KnownValues as KV
import qualified G2.Language.ExprEnv as E

import G2.Execution

import G2.Initialization.MkCurrExpr
import qualified G2.Initialization.Types as T (expr_env)

import G2.Liquid.AddCFBranch
import G2.Liquid.AddLHTC
import G2.Liquid.AddOrdToNum
import G2.Liquid.AddTyVars
import G2.Liquid.Conversion
import G2.Liquid.ConvertCurrExpr
import G2.Liquid.Helpers
import G2.Liquid.LHReducers
import G2.Liquid.Measures
import G2.Liquid.MkLHVals
import G2.Liquid.G2Calls
import G2.Liquid.Simplify
import G2.Liquid.SpecialAsserts
import G2.Liquid.TCGen
import G2.Liquid.TCValues
import G2.Liquid.Types
import G2.Liquid.TyVarBags
import G2.Solver hiding (solve)

import G2.Lib.Printers

import Language.Haskell.Liquid.Types hiding (Config, cls, names)
import qualified Language.Haskell.Liquid.Types.PrettyPrint as PPR
import Language.Haskell.Liquid.UX.CmdLine

import qualified Language.Fixpoint.Types.PrettyPrint as FPP

import Control.Exception
import Control.Monad.Extra
import Data.List
import qualified Data.HashSet as S
import qualified Data.Map as M
import qualified Data.Text as T
import qualified Data.Text.IO as TI

import Var

import G2.Language.KnownValues

import Debug.Trace
import G2.Language.Monad

data LHReturn = LHReturn { calledFunc :: FuncInfo
                         , violating :: Maybe FuncInfo
                         , abstracted :: [FuncInfo] } deriving (Eq, Show)

data FuncInfo = FuncInfo { func :: T.Text
                         , funcArgs :: T.Text
                         , funcReturn :: T.Text } deriving (Eq, Show)

-- | findCounterExamples
-- Given (several) LH sources, and a string specifying a function name,
-- attempt to find counterexamples to the functions liquid type
findCounterExamples :: [FilePath] -> [FilePath] -> T.Text -> [FilePath] -> [FilePath] -> Config -> IO (([ExecRes AbstractedInfo], Bindings), Lang.Id)
findCounterExamples proj fp entry libs lhlibs config = do
    let config' = config { mode = Liquid }

    lh_config <- getOpts []

    ghci <- try $ getGHCInfos lh_config proj fp lhlibs :: IO (Either SomeException [GhcInfo])
    
    let ghci' = case ghci of
                  Right g_c -> g_c
                  Left e -> error $ "ERROR OCCURRED IN LIQUIDHASKELL\n" ++ show e

    tgt_trans <- translateLoaded proj fp libs (simplTranslationConfig { simpl = False }) config'

    runLHCore entry tgt_trans ghci' config'

runLHCore :: T.Text -> (Maybe T.Text, ExtractedG2)
                    -> [GhcInfo]
                    -> Config
                    -> IO (([ExecRes AbstractedInfo], Bindings), Lang.Id)
runLHCore entry (mb_modname, exg2) ghci config = do
    LiquidData { ls_state = final_st
               , ls_bindings = bindings
               , ls_id = ifi
               , ls_counterfactual_name = cfn
               , ls_counterfactual_funcs = fs
               , ls_memconfig = pres_names } <- liquidStateWithCall entry (mb_modname, exg2) ghci config mempty

    SomeSolver solver <- initSolver config
    let simplifier = ADTSimplifier arbValue

    let (red, hal, ord) = lhReducerHalterOrderer config solver simplifier entry mb_modname cfn final_st
    (exec_res, final_bindings) <- runLHG2 config red hal ord solver simplifier pres_names ifi final_st bindings

    close solver

    return ((exec_res, final_bindings), ifi)

{-# INLINE liquidStateWithCall #-}
liquidStateWithCall :: T.Text -> (Maybe T.Text, ExtractedG2)
                      -> [GhcInfo]
                      -> Config
                      -> MemConfig
                      -> IO LiquidData
liquidStateWithCall entry (mb_modname, exg2) ghci config memconfig =
    liquidStateWithCall' entry (mb_modname, exg2) ghci config memconfig (mkCurrExpr Nothing Nothing) mkArgTys

{-# INLINE liquidStateWithCall' #-}
liquidStateWithCall' :: T.Text -> (Maybe T.Text, ExtractedG2)
                       -> [GhcInfo]
                       -> Config
                       -> MemConfig
                       -> (Lang.Id -> MkCurrExpr)
                       -> (Lang.Expr -> MkArgTypes)
                       -> IO LiquidData
liquidStateWithCall' entry (mb_m, exg2) ghci config memconfig mkCurr argTys = do
    let simp_s = initSimpleState exg2
    liquidStateFromSimpleStateWithCall' simp_s ghci entry mb_m config memconfig mkCurr argTys

{-# INLINE liquidStateFromSimpleStateWithCall #-}
liquidStateFromSimpleStateWithCall :: SimpleState
                                   -> [GhcInfo]
                                   -> T.Text
                                   -> Maybe T.Text
                                   -> Config
                                   -> MemConfig
                                   -> IO LiquidData
liquidStateFromSimpleStateWithCall simp_s ghci entry mb_m config memconfig =
    liquidStateFromSimpleStateWithCall' simp_s ghci entry mb_m config memconfig (mkCurrExpr Nothing Nothing) mkArgTys

{-# INLINE liquidStateFromSimpleStateWithCall' #-}
liquidStateFromSimpleStateWithCall' :: SimpleState
                                    -> [GhcInfo]
                                    -> T.Text
                                    -> Maybe T.Text
                                    -> Config
                                    -> MemConfig
                                    -> (Lang.Id -> MkCurrExpr)
                                    -> (Lang.Expr -> MkArgTypes)
                                    -> IO LiquidData
liquidStateFromSimpleStateWithCall' simp_s ghci entry mb_m config memconfig mkCurr argTys = do
    let (simp_s', ph_tyvars) = if add_tyvars config
                                  then fmap Just $ addTyVarsEEnvTEnv simp_s
                                  else (simp_s, Nothing)
        (s, i, bindings') = initStateFromSimpleStateWithCall simp_s' True entry mb_m mkCurr argTys config
    
    fromLiquidReadyState s i bindings' ghci ph_tyvars config memconfig

{-# INLINE liquidStateFromSimpleState #-}
liquidStateFromSimpleState :: SimpleState
                            -> [GhcInfo]
                            -> Config
                            -> MemConfig
                            -> MkCurrExpr
                            -> MkArgTypes
                            -> IO LiquidData
liquidStateFromSimpleState simp_s ghci config memconfig mkCurr argTys = do
    let (simp_s', ph_tyvars) = if add_tyvars config
                                  then fmap Just $ addTyVarsEEnvTEnv simp_s
                                  else (simp_s, Nothing)
        (s, bindings') = initStateFromSimpleState simp_s' True mkCurr argTys config
    
    fromLiquidReadyState s (Id (Name "" Nothing 0 Nothing) TyUnknown) bindings' ghci ph_tyvars config memconfig

{-# INLINE fromLiquidReadyState #-}
fromLiquidReadyState :: State ()
                     -> Lang.Id
                     -> Bindings
                     -> [GhcInfo]
                     -> Maybe PhantomTyVars
                     -> Config
                     -> MemConfig
                     -> IO LiquidData
fromLiquidReadyState init_state ifi bindings ghci ph_tyvars config memconfig = do
    let (init_state', bindings') = (markAndSweepPreserving (reqNames init_state `mappend` memconfig) init_state bindings)
        cleaned_state = init_state' { type_env = type_env init_state } 
    fromLiquidNoCleaning cleaned_state ifi bindings' ghci ph_tyvars config memconfig

data LiquidReadyState = LiquidReadyState { lr_state :: LHState
                                         , lr_binding :: Bindings
                                         , lr_known_values :: KnownValues
                                         , lr_type_classes :: TypeClasses
                                         , lr_higher_ord_insts :: S.HashSet Name }

data LiquidData = LiquidData { ls_state :: State LHTracker
                             , ls_bindings :: Bindings
                             , ls_id :: Lang.Id
                             , ls_counterfactual_name :: CounterfactualName
                             , ls_counterfactual_funcs :: S.HashSet Name
                             , ls_measures :: Measures
                             , ls_assumptions :: Assumptions
                             , ls_posts :: Posts
                             , ls_tcv :: TCValues
                             , ls_memconfig :: MemConfig }

cleanReadyState :: LiquidReadyState -> MemConfig -> LiquidReadyState
cleanReadyState lrs@(LiquidReadyState { lr_state = lhs@(LHState { state = s }), lr_binding = b }) memconfig =
    let
        (s', b') = (markAndSweepPreserving (reqNames s `mappend` memconfig) s b)
        s'' = s' { type_env = type_env s }
    in
    lrs { lr_state = lhs { state = s'' }, lr_binding = b' }

fromLiquidNoCleaning :: State ()
                     -> Lang.Id
                     -> Bindings
                     -> [GhcInfo]
                     -> Maybe PhantomTyVars
                     -> Config
                     -> MemConfig
                     -> IO LiquidData
fromLiquidNoCleaning init_state ifi bindings ghci ph_tyvars config memconfig = do
    let lrs = createLiquidReadyState init_state bindings ghci ph_tyvars config
    processLiquidReadyState lrs ifi ghci config memconfig

createLiquidReadyState :: State () -> Bindings -> [GhcInfo] -> Maybe PhantomTyVars -> Config -> LiquidReadyState
createLiquidReadyState s@(State {expr_env = eenv}) bindings ghci ph_tyvars config =
    let
        np_ng = name_gen bindings

        (meenv, mkv, mtc, minst, mexported, ng') = mkLHVals s (higher_order_inst bindings) (exported_funcs bindings) np_ng 

        s' = s { track = [] }
        bindings' = bindings { exported_funcs = mexported ++ exported_funcs bindings, name_gen = ng' }

        (lh_state, lh_bindings) = createLHState meenv mkv mtc s' bindings'

        (data_state, data_bindings) = execLHStateM (initializeLHData ghci ph_tyvars config) lh_state lh_bindings
    in
    LiquidReadyState { lr_state = data_state
                     , lr_binding = data_bindings
                     , lr_known_values = mkv
                     , lr_type_classes = mtc
                     , lr_higher_ord_insts = minst } -- (mkv, mtc, minst, data_state, data_bindings)

processLiquidReadyStateCleaning :: LiquidReadyState -> Lang.Id -> [GhcInfo] -> Config -> MemConfig -> IO LiquidData
processLiquidReadyStateCleaning lrs ifi ghci config memconfig =
    let
        lrs' = cleanReadyState lrs memconfig
    in
    processLiquidReadyState lrs' ifi ghci config memconfig

processLiquidReadyState :: LiquidReadyState -> Lang.Id -> [GhcInfo] -> Config -> MemConfig -> IO LiquidData
processLiquidReadyState lrs@(LiquidReadyState { lr_state = lh_state
                                              , lr_binding = lh_bindings
                                              , lr_known_values = mkv
                                              , lr_type_classes = mtc
                                              , lr_higher_ord_insts = minst}) ifi ghci config memconfig = do
    let ((cfn, mc, cff), (merged_state, bindings')) = runLHStateM (initializeLHSpecs (counterfactual config) ghci ifi lh_bindings) lh_state lh_bindings
        lrs' = lrs { lr_state = merged_state, lr_binding = bindings'}

    lhs <- extractWithoutSpecs lrs' ifi ghci config memconfig
    
    let lh_s = if only_top config
                  then elimNonTop (S.insert (idName mc) cff) (ls_state lhs)
                  else ls_state lhs

    return $ lhs { ls_state = lh_s
                 , ls_id = mc
                 , ls_counterfactual_name = cfn
                 , ls_counterfactual_funcs = cff }

extractWithoutSpecs :: LiquidReadyState -> Lang.Id -> [GhcInfo] -> Config -> MemConfig -> IO LiquidData
extractWithoutSpecs lrs@(LiquidReadyState { lr_state = s
                                          , lr_binding = bindings
                                          , lr_known_values = mkv
                                          , lr_type_classes = mtc
                                          , lr_higher_ord_insts = minst}) ifi ghci config memconfig = do
    let (lh_s, bindings') = execLHStateM (return ()) s bindings
    let bindings'' = bindings' { higher_order_inst = minst }

    let tcv = tcvalues lh_s
    let lh_s' = deconsLHState lh_s

    let annm = annots lh_s
        pres_names = addSearchNames (names tcv ++ names mkv) $ reqNames lh_s'
        pres_names' = addSearchNames (names annm) pres_names

    let track_state = lh_s' {track = LHTracker { abstract_calls = []
                                               , last_var = Nothing
                                               , annotations = annm
                                               , all_calls = [] } }

    -- We replace certain function name lists in the final State with names
    -- mapping into the measures from the LHState.  These functions do not
    -- need to be passed the LH typeclass, so this ensures use of Names from
    -- these lists will work, without us having to modify all of G2 to account
    -- for the LH typeclass.
    let final_st = track_state { known_values = mkv
                               , type_classes = unionTypeClasses mtc (type_classes track_state)}

    let real_meas = lrsMeasures ghci lrs


    return $ LiquidData { ls_state = final_st
                        , ls_bindings = bindings''
                        , ls_id = ifi
                        , ls_counterfactual_name = error "No counterfactual name"
                        , ls_counterfactual_funcs = error "No counterfactual funcs"
                        , ls_measures = real_meas
                        , ls_assumptions = assumptions lh_s
                        , ls_posts = posts lh_s
                        , ls_tcv = tcv
                        , ls_memconfig = pres_names' `mappend` memconfig }

lrsMeasures :: [GhcInfo] -> LiquidReadyState -> Measures
lrsMeasures ghci lrs = 
    let
        meas_names = measureNames ghci
        meas_nameOcc = map (\(Name n md _ _) -> (n, md)) $ map symbolName meas_names

        real_meas = E.filterWithKey (\(Name n md i _) _ -> 
                                (n, md) `elem` meas_nameOcc && i == 0) . measures $ lr_state lrs
    in
    real_meas

processLiquidReadyStateWithCall :: LiquidReadyState -> [GhcInfo] -> T.Text -> Maybe T.Text-> Config -> MemConfig -> IO LiquidData
processLiquidReadyStateWithCall lrs@(LiquidReadyState { lr_state = lhs@(LHState { state = s })
                                                      , lr_binding = bindings})
                                                                ghci f m_mod config memconfig = do

    let (ie, fe) = case findFunc f m_mod (expr_env s) of
                          Left ie' -> ie'
                          Right errs -> error errs

        (ce, is, f_i, ng') = mkCurrExpr Nothing Nothing ie (type_classes s) (name_gen bindings)
                                      (expr_env s) (deepseq_walkers bindings) (known_values s) config

        lhs' = lhs { state = s { expr_env = foldr (\i@(Id n _) -> E.insertSymbolic n i) (expr_env s) is
                               , curr_expr = CurrExpr Evaluate ce
                               , symbolic_ids = is }
                   }
        (lhs'', bindings') = execLHStateM (addLHTCCurrExpr) lhs' (bindings { name_gen = ng' })

        lrs' = lrs { lr_state = lhs''
                   , lr_binding = bindings' { fixed_inputs = f_i
                                            , input_names = map idName is
                                            }
                   }

    processLiquidReadyStateCleaning lrs' ie ghci config memconfig

runLHG2 :: (Solver solver, Simplifier simplifier)
        => Config
        -> SomeReducer LHTracker
        -> SomeHalter LHTracker
        -> SomeOrderer LHTracker
        -> solver
        -> simplifier
        -> MemConfig
        -> Lang.Id
        -> State LHTracker
        -> Bindings
        -> IO ([ExecRes AbstractedInfo], Bindings)
runLHG2 config red hal ord solver simplifier pres_names init_id final_st bindings = do
    let only_abs_st = addTicksToDeepSeqCases (deepseq_walkers bindings) final_st
    (ret, final_bindings) <- runG2WithSomes red hal ord solver simplifier pres_names only_abs_st bindings
    let n_ret = map (\er -> er { final_state = putSymbolicExistentialInstInExprEnv (final_state er) }) ret

    -- We filter the returned states to only those with the minimal number of abstracted functions
    let mi = case length n_ret of
                  0 -> 0
                  _ -> minimum $ map (\(ExecRes {final_state = s}) -> abstractCallsNum s) n_ret
    let ret' = map (\er -> if fmap funcName (violated er) == Just initiallyCalledFuncName
                                  then er { violated = Nothing }
                                  else er) n_ret
    let ret'' = filter (\(ExecRes {final_state = s}) -> mi == (abstractCallsNum s)) ret'

    (bindings', ret''') <- mapAccumM (reduceCalls solver simplifier config) final_bindings ret''
    ret'''' <- mapM (checkAbstracted solver simplifier config init_id bindings') ret'''

    let exec_res = 
          map (\(ExecRes { final_state = s
                         , conc_args = es
                         , conc_out = e
                         , violated = ais}) ->
                (ExecRes { final_state =
                              s {track = 
                                    mapAbstractedInfoFCs (subVarFuncCall (model s) (expr_env s) (type_classes s))
                                    $ track s
                                }
                         , conc_args = es
                         , conc_out = e
                         , violated = ais})) ret''''

    return (exec_res, final_bindings)


lhReducerHalterOrderer :: (Solver solver, Simplifier simplifier)
                       => Config
                       -> solver
                       -> simplifier
                       -> T.Text
                       -> Maybe T.Text
                       -> CounterfactualName
                       -> State t
                       -> (SomeReducer LHTracker, SomeHalter LHTracker, SomeOrderer LHTracker)
lhReducerHalterOrderer config solver simplifier entry mb_modname cfn st =
    let
        ng = mkNameGen ()

        share = sharing config

        (limHalt, limOrd) = limitByAccepted (cut_off config)
        state_name = Name "state" Nothing 0 Nothing

        abs_ret_name = Name "abs_ret" Nothing 0 Nothing
    in
    if higherOrderSolver config == AllFuncs then
        ( SomeReducer NonRedPCRed
            <~| (SomeReducer (NonRedAbstractReturns :<~| TaggerRed abs_ret_name ng ))
            <~| (case logStates config of
                  Just fp -> SomeReducer (StdRed share solver simplifier :<~| LHRed cfn :<~? ExistentialInstRed :<~ Logger fp)
                  Nothing -> SomeReducer (StdRed share solver simplifier :<~| LHRed cfn :<~? ExistentialInstRed))
        , SomeHalter
                (MaxOutputsHalter (maxOutputs config)
                  :<~> ZeroHalter (steps config)
                  :<~> LHAbsHalter entry mb_modname (expr_env st)
                  :<~> limHalt
                  :<~> SwitchEveryNHalter (switch_after config)
                  :<~> LHAcceptIfViolatedHalter)
        , SomeOrderer limOrd)
    else
        (SomeReducer (NonRedAbstractReturns :<~| TaggerRed abs_ret_name ng)
            <~| (SomeReducer (NonRedPCRed :<~| TaggerRed state_name ng))
            <~| (case logStates config of
                  Just fp -> SomeReducer (StdRed share solver simplifier :<~| LHRed cfn :<~? ExistentialInstRed :<~ Logger fp)
                  Nothing -> SomeReducer (StdRed share solver simplifier :<~| LHRed cfn :<~? ExistentialInstRed)) -- :<~ LimLogger 0 700 [2, 1, 2, 2, 1, 1, 1] "aMapReduce"))
        , SomeHalter
            (DiscardIfAcceptedTag state_name
              :<~> DiscardIfAcceptedTag abs_ret_name
              :<~> MaxOutputsHalter (maxOutputs config)
              :<~> ZeroHalter (steps config)
              :<~> LHAbsHalter entry mb_modname (expr_env st)
              :<~> limHalt
              :<~> SwitchEveryNHalter (switch_after config)
              :<~> LHAcceptIfViolatedHalter)
        , SomeOrderer limOrd)


initializeLH :: Counterfactual -> [GhcInfo] -> Maybe PhantomTyVars -> Lang.Id -> Bindings -> Config -> LHStateM (Lang.Name, Lang.Id, S.HashSet Lang.Name)
initializeLH counter ghcInfos ph_tyvars ifi bindings config = do
    initializeLHData ghcInfos ph_tyvars config
    initializeLHSpecs counter ghcInfos ifi bindings

initializeLHData :: [GhcInfo] -> Maybe PhantomTyVars -> Config -> LHStateM ()
initializeLHData ghcInfos m_ph_tyvars config = do
    addLHTC
    addOrdToNum

    addErrorAssumes config

    let lh_measures = measureSpecs ghcInfos

    meenv <- measuresM
    nt <- return . M.fromList =<< mapMaybeM measureTypeMappings lh_measures
    fil_meenv <- filterMeasures' meenv (M.keys nt)

    createMeasures lh_measures

    case m_ph_tyvars of
      Just ph_tyvars -> addTyVarsMeasures ph_tyvars
      Nothing -> return ()

    meenv' <- measuresM
    putMeasuresM (fil_meenv `E.union` meenv')

-- | Returns the name of the Tick on the counterfactual branches, and the names
-- of all functions with counterfactual branches
initializeLHSpecs :: Counterfactual -> [GhcInfo] -> Lang.Id -> Bindings -> LHStateM (Lang.Name, Lang.Id, S.HashSet Lang.Name)
initializeLHSpecs counter ghcInfos ifi bindings = do
    (CurrExpr er ce) <- currExpr
    let specs = funcSpecs ghcInfos
    mergeLHSpecState specs

    (CurrExpr er ce') <- currExpr
    addSpecialAsserts
    addTrueAsserts (idName ifi)

    -- Most of the simplification works less well on some of the Core generated by convertCurrExpr,
    -- so we apply the simplification first.  However, we do want to stamp out as much redundancy
    -- from convertCurrExpr as we can, so we do further simplificiation after
    simplify
    (main_call, ns) <- convertCurrExpr ifi bindings
    furtherSimplifyCurrExpr

    (cfn, ns') <- case counter of
                    Counterfactual cf_mods ->
                        return . (,ns) =<< addCounterfactualBranch cf_mods ns
                    NotCounterfactual -> return (Name "" Nothing 0 Nothing, [])

    mapME (return . flattenLets)

    return (cfn, main_call, S.fromList ns')

reqNames :: State t -> MemConfig
reqNames (State { expr_env = eenv
                , type_env = tenv
                , type_classes = tc
                , known_values = kv}) =
    let ns = Lang.names
                   [ mkGe kv eenv
                   , mkGt kv eenv
                   , mkEq kv eenv
                   , mkNeq kv eenv
                   , mkLt kv eenv
                   , mkLe kv eenv
                   , mkAnd kv eenv
                   , mkOr kv eenv
                   , mkNot kv eenv
                   , mkPlus kv eenv
                   , mkMinus kv eenv
                   , mkMult kv eenv
                   -- , mkDiv kv eenv
                   , mkMod kv eenv
                   , mkNegate kv eenv
                   , mkImplies kv eenv
                   , mkIff kv eenv
                   , mkFromInteger kv eenv
                   -- , mkToInteger kv eenv

                   , mkJust kv tenv
                   , mkNothing kv tenv

                   , mkUnit kv tenv

                   , mkIntegralExtactReal kv
                   , mkRealExtractNum kv 
                   ]
          ++
          Lang.names 
            (M.filterWithKey 
                (\k _ -> k == eqTC kv || k == numTC kv || k == ordTC kv || k == integralTC kv || k == fractionalTC kv || k == structEqTC kv) 
                (toMap tc)
            )
    in
    MemConfig { search_names = ns
              , pres_func = pf }
    where
        pf _ (Bindings { deepseq_walkers = dsw }) a =
            S.fromList . map idName . M.elems $ M.filterWithKey (\n _ -> n `S.member` a) dsw

pprint :: (Var, LocSpecType) -> IO ()
pprint (v, r) = do
    let i = mkIdUnsafe v

    let doc = PPR.rtypeDoc FPP.Full $ val r
    putStrLn $ show i
    putStrLn $ show doc

printLHOut :: Lang.Id -> [ExecRes AbstractedInfo] -> IO ()
printLHOut entry =
    mapM_ (\s -> do printParsedLHOut s; putStrLn "") . map (parseLHOut entry)

printCE :: [CounterExample] -> IO ()
printCE =
    mapM_ (\s -> do printParsedLHOut s; putStrLn "") . map counterExampleToLHReturn

printParsedLHOut :: LHReturn -> IO ()
printParsedLHOut (LHReturn { calledFunc = FuncInfo {func = f, funcArgs = call, funcReturn = output}
                           , violating = Nothing
                           , abstracted = abstr}) = do
    putStrLn "The call"
    TI.putStrLn $ call `T.append` " = " `T.append` output
    TI.putStrLn $ "violates " `T.append` f `T.append` "'s refinement type"
    printAbs abstr
printParsedLHOut (LHReturn { calledFunc = FuncInfo {funcArgs = call, funcReturn = output}
                           , violating = Just (FuncInfo {func = f, funcArgs = call', funcReturn = output'})
                           , abstracted = abstr }) = do
    TI.putStrLn $ call `T.append` " = " `T.append` output
    putStrLn "makes a call to"
    TI.putStrLn $ call' `T.append` " = " `T.append` output'
    TI.putStrLn $ "violating " `T.append` f `T.append` "'s refinement type"
    printAbs abstr

printAbs :: [FuncInfo] -> IO ()
printAbs fi = do
    let fn = T.intercalate ", " $ map func fi

    if length fi > 0 then do
        putStrLn "if"
        mapM_ printFuncInfo fi
        if length fi > 1 then do
            TI.putStrLn $ "Strengthen the refinement types of " `T.append`
                          fn `T.append` " to eliminate these possibilities"
            putStrLn "Abstract"
        else do
            TI.putStrLn $ "Strengthen the refinement type of " `T.append`
                          fn `T.append` " to eliminate this possibility"
            putStrLn "Abstract"
    else
        putStrLn "Concrete"

printFuncInfo :: FuncInfo -> IO ()
printFuncInfo (FuncInfo {funcArgs = call, funcReturn = output}) =
    TI.putStrLn $ call `T.append` " = " `T.append` output

parseLHOut :: Lang.Id -> ExecRes AbstractedInfo -> LHReturn
parseLHOut entry (ExecRes { final_state = s
                          , conc_args = inArg
                          , conc_out = ex
                          , violated = ais}) =
  let
      called = funcCallToFuncInfo  (T.pack . mkCleanExprHaskell s)
             $ FuncCall { funcName = idName entry, arguments = inArg, returns = ex}
      viFunc = fmap (parseLHFuncTuple s) ais

      abstr = map (parseLHFuncTuple s) . map abstract . abs_calls $ track s
  in
  LHReturn { calledFunc = called
           , violating = viFunc
           , abstracted = abstr}

counterExampleToLHReturn :: CounterExample -> LHReturn
counterExampleToLHReturn (DirectCounter fc abstr) =
    let
        called = funcCallToFuncInfo (T.pack . mkExprHaskell) . abstract $ fc
        abstr' = map (funcCallToFuncInfo (T.pack . mkExprHaskell) . abstract) abstr
    in
    LHReturn { calledFunc = called
             , violating = Nothing
             , abstracted = abstr'}
counterExampleToLHReturn (CallsCounter fc viol_fc abstr) =
    let
        called = funcCallToFuncInfo (T.pack . mkExprHaskell) . abstract $ fc
        viol_called = funcCallToFuncInfo (T.pack . mkExprHaskell) . abstract $ viol_fc
        abstr' = map (funcCallToFuncInfo (T.pack . mkExprHaskell) . abstract) abstr
    in
    LHReturn { calledFunc = called
             , violating = Just viol_called
             , abstracted = abstr'}

funcCallToFuncInfo :: (Expr -> T.Text) -> FuncCall -> FuncInfo
funcCallToFuncInfo t (FuncCall { funcName = f, arguments = inArg, returns = ret }) =
    let
        funcCall = t . foldl (\a a' -> App a a') (Var (Id f TyUnknown)) $ inArg
        funcOut = t ret
    in
    FuncInfo {func = nameOcc f, funcArgs = funcCall, funcReturn = funcOut}

lhStateToCE :: Lang.Id -> ExecRes AbstractedInfo -> CounterExample
lhStateToCE i (ExecRes { final_state = s@State { track = t }
                       , conc_args = inArg
                       , conc_out = ex})
    | Nothing <- abs_violated t = DirectCounter (init_call t) (abs_calls t)
    | Just c <-  abs_violated t = CallsCounter (init_call t) c (abs_calls t)

parseLHFuncTuple :: State t -> FuncCall -> FuncInfo
parseLHFuncTuple s (FuncCall {funcName = n, arguments = ars, returns = out}) =
    let
        t = case fmap typeOf $ E.lookup n (expr_env s) of
                  Just t' -> t'
                  Nothing -> error $ "Unknown type for abstracted function " ++ show n
    in
    FuncInfo { func = nameOcc n
             , funcArgs = T.pack $ mkCleanExprHaskell s (foldl' App (Var (Id n t)) ars)
             , funcReturn = T.pack $ mkCleanExprHaskell s out }
