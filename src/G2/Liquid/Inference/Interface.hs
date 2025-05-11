{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module G2.Liquid.Inference.Interface ( inferenceCheck
                                     , inference
                                     , getInitState
                                     , getNameLevels ) where

import G2.Config.Config as G2
import G2.Data.Timer
import G2.Interface hiding (violated)
import G2.Language.CallGraph
import G2.Language.Expr
import qualified G2.Language.ExprEnv as E
import G2.Language.Naming
import G2.Language.Support
import G2.Language.Syntax
import G2.Language.Typing
import G2.Liquid.Config
import G2.Liquid.ConvertCurrExpr
import G2.Liquid.Helpers
import G2.Liquid.Inference.Config
import G2.Liquid.Inference.FuncConstraint as FC
import G2.Liquid.Inference.G2Calls
import G2.Liquid.Inference.InfStack
import G2.Liquid.Inference.Initalization
import G2.Liquid.Inference.PolyRef
import G2.Liquid.Inference.Sygus
import G2.Liquid.Inference.UnionPoly
import G2.Liquid.Inference.GeneratedSpecs
import G2.Liquid.Inference.Verify
import G2.Liquid.Interface
import G2.Liquid.Types hiding (state)
import qualified G2.Liquid.Types as T
import qualified G2.Liquid.Types as G2LH
import G2.Solver
import G2.Translation

import Language.Haskell.Liquid.Types as LH

import Control.Monad.IO.Class 
import Control.Monad.Reader
import Data.Either
import qualified Data.HashSet as S
import qualified Data.HashMap.Lazy as HM
import Data.List
import Data.Maybe
import qualified Data.Text as T
import qualified Data.Text.IO as T
import qualified G2.Language.TyVarEnv as TV 

-- Run inference, with an extra, final check of correctness at the end.
-- Assuming inference is working correctly, this check should neve fail.
inferenceCheck :: InferenceConfig -> G2.Config -> LHConfig ->  [FilePath] -> [FilePath] -> IO (State [FuncCall], Either [CounterExample] GeneratedSpecs)
inferenceCheck infconfig config g2lhconfig proj fp = do
    (ghci, lhconfig) <- getGHCI infconfig proj fp
    (s, res, _, loops) <- inference' infconfig config g2lhconfig lhconfig ghci proj fp
    print $ loop_count loops
    print . sum . HM.elems $ loop_count loops
    print $ backtracks loops
    print $ searched_below loops
    print $ negated_models loops
    case res of
        Right gs -> do
            check_res <- checkGSCorrect infconfig lhconfig ghci gs
            case check_res of
                Safe -> return (s, res)
                _ -> error "inferenceCheck: Check failed"
        _ -> return (s, res)

inference :: InferenceConfig -> G2.Config -> LHConfig ->  [FilePath] -> [FilePath] -> IO (State [FuncCall], Either [CounterExample] GeneratedSpecs)
inference infconfig config g2lhconfig proj fp = do
    -- Initialize LiquidHaskell
    (ghci, lhconfig) <- getGHCI infconfig proj fp
    (s, res, timer, _) <- inference' infconfig config g2lhconfig lhconfig ghci proj fp
    print . logToSecs . sumLog . getLog $ timer
    return (s, res)

inference' :: InferenceConfig
           -> G2.Config
           -> LHConfig
           -> LH.Config
           -> [GhcInfo]
           -> [FilePath]
           -> [FilePath]
           -> IO (State [FuncCall], Either [CounterExample] GeneratedSpecs, Timer (Event Name), Counters)
inference' infconfig config g2lhconfig lhconfig ghci proj fp = do
    mapM_ (print . getQualifiers) ghci

    (lrs, g2config', g2lhconfig', infconfig', main_mod) <- getInitState proj fp ghci infconfig config g2lhconfig
    let nls = getNameLevels (head main_mod) lrs

    let ut = sharedTyConsEE (tyvar_env . G2LH.state . lr_state $ lrs) (concat nls) (expr_env . G2LH.state . lr_state $ lrs)

    let configs = Configs { g2_config = g2config', g2lh_config = g2lhconfig', lh_config = lhconfig, inf_config = infconfig'}
        prog = newProgress

    SomeSMTSolver solver <- getSMT g2config'
    let infL = iterativeInference solver ghci (head main_mod) lrs nls HM.empty emptyGS emptyFC ut

    (res, ev_timer, lvl_timer, loops) <- runInfStack configs prog infL -- runProgresser (runConfigs (runTimer infL timer) configs) prog

    print . logToSecs . orderLogBySpeed . sumLog . getLog $ lvl_timer

    print . logToSecs . orderLogBySpeed . sumLog . mapLabels (mapEvent nameOcc) . getLog $ ev_timer
    print . logToSecs . orderLogBySpeed . sumLog . mapLabels (mapEvent (const ())) . getLog $ ev_timer
    return (G2LH.state . lr_state $ lrs, res, ev_timer, loops)

getInitState :: [FilePath]
             -> [FilePath]
             -> [GhcInfo]
             -> InferenceConfig
             -> G2.Config
             -> LHConfig
             -> IO (LiquidReadyState, G2.Config, LHConfig, InferenceConfig, [Maybe T.Text])
getInitState proj fp ghci infconfig config lhconfig = do
    let g2config = config { mode = Liquid
                          , steps = 2000 }
        transConfig = simplTranslationConfig { simpl = False }
    (main_mod, exg2) <- translateLoaded proj fp transConfig g2config
    -- TODO: is it safe to include the have TV.empty
    let (lrs, g2config', lhconfig', infconfig') = initStateAndConfig TV.empty exg2 main_mod g2config lhconfig infconfig ghci
    return (lrs, g2config', lhconfig', infconfig', main_mod)

getNameLevels :: Maybe T.Text -> LiquidReadyState -> NameLevels
getNameLevels main_mod =
    filter (not . null)
       . map nub
       . nameLevels
       . getCallGraph
       . E.filterWithKey (\(Name _ m _ _) _ -> m == main_mod)
       . expr_env . G2LH.state . lr_state


data InferenceRes = CEx [CounterExample]
                  | Env GeneratedSpecs FuncConstraints MaxSizeConstraints MeasureExs
                  | Raise MeasureExs FuncConstraints MaxSizeConstraints
                  deriving (Show)

type NameLevels = [[Name]]

type MaxSizeConstraints = FuncConstraints

iterativeInference :: (MonadIO m, SMTConverter con)
                   => con
                   -> [GhcInfo]
                   -> Maybe T.Text
                   -> LiquidReadyState
                   -> NameLevels
                   -> MeasureExs
                   -> GeneratedSpecs
                   -> FuncConstraints
                   -> UnionedTypes
                   -> InfStack m (Either [CounterExample] GeneratedSpecs)
iterativeInference con ghci m_modname lrs nls meas_ex gs fc ut = do
    res <- inferenceL con FirstRound ghci m_modname lrs nls emptyEvals meas_ex gs fc emptyFC ut emptyBlockedModels
    case res of
        CEx cex -> return $ Left cex
        Env n_gs _ _ _ -> return $ Right n_gs
        Raise _ r_fc _ -> do
            incrMaxDepthI
            -- We might be missing some internal GHC types from our type_env
             -- We filter them out to avoid an error
            let eenv = expr_env . G2LH.state $ lr_state lrs
                chck = filter (\n -> 
                                   case E.lookup n eenv of
                                       Just e | TyCon tcn _ <- returnType $ typeOf (tyvar_env  . G2LH.state $ lr_state lrs) e -> isJust $ HM.lookup tcn (type_env  . G2LH.state $ lr_state lrs)  
                                       _ -> False) (head nls)
            liftIO . putStrLn $ "head nls =  " ++ show (head nls)
            logEventStartM CExSE
            ref <- getCEx ghci m_modname lrs gs chck
            logEventEndM
            case ref of
                Left cex -> return $ Left cex
                Right fc' -> do
                    logEventStartM UpdateMeasures
                    logEventEndM
                    incrMaxSynthSizeI
                    r_meas_ex' <- lift . lift . lift $ updateMeasureExs {- r_meas_ex -} HM.empty lrs ghci {- fc' -} (unionFC fc' r_fc)
                    iterativeInference con ghci m_modname lrs nls r_meas_ex' gs (unionFC fc' r_fc) ut


inferenceL :: (MonadIO m, SMTConverter con)
           => con
           -> Iteration
           -> [GhcInfo]
           -> Maybe T.Text
           -> LiquidReadyState
           -> NameLevels
           -> Evals Bool
           -> MeasureExs
           -> GeneratedSpecs
           -> FuncConstraints
           -> MaxSizeConstraints
           -> UnionedTypes
           -> BlockedModels
           -> InfStack m InferenceRes
inferenceL con iter ghci m_modname lrs nls evals meas_ex senv fc max_fc ut blk_mdls = do
    let sf = case nls of
                        (_:sf_:_) -> sf_
                        ([_])-> []
                        [] -> []

    startLevelTimer (case nls of fs_:_ -> fs_; [] -> [])
    (resAtL, evals') <- inferenceB con iter ghci m_modname lrs nls evals meas_ex senv fc max_fc ut blk_mdls
    endLevelTimer

    liftIO $ do
        putStrLn "-------"
        putStrLn $ "lengths = " ++ show (HM.map (length . nub) (blockedHashMap blk_mdls))
        putStrLn "-------"

    case resAtL of
        Env senv' n_fc n_mfc meas_ex' -> 
            case nls of
                [] -> return resAtL
                (_:nls') -> do
                    liftIO $ putStrLn "Down a level!"
                    let evals'' = foldr deleteEvalsForFunc evals' sf
                    inf_res <- inferenceL con FirstRound ghci m_modname lrs nls' evals'' meas_ex' senv'
                                                        (unionFC fc n_fc) (unionFC max_fc n_mfc) ut emptyBlockedModels
                    case inf_res of
                        Raise r_meas_ex r_fc r_max_fc -> do
                            liftIO $ putStrLn "Up a level!"
                            
                            inferenceL con AfterFirstRound ghci m_modname lrs nls evals' r_meas_ex senv r_fc r_max_fc ut blk_mdls
                        _ -> return inf_res
        _ -> return resAtL

inferenceB :: (MonadIO m, SMTConverter con)
           => con
           -> Iteration
           -> [GhcInfo]
           -> Maybe T.Text
           -> LiquidReadyState
           -> NameLevels
           -> Evals Bool
           -> MeasureExs
           -> GeneratedSpecs
           -> FuncConstraints
           -> MaxSizeConstraints
           -> UnionedTypes
           -> BlockedModels
           -> InfStack m (InferenceRes, Evals Bool)
inferenceB con iter ghci m_modname lrs nls evals meas_ex gs fc max_fc ut blk_mdls = do
    let (fs, sf, below_sf) = case nls of
                        (fs_:sf_:be) -> (fs_, sf_, be)
                        ([fs_])-> (fs_, [], [])
                        [] -> ([], [], [])

    incrLoopCountLog fs

    let curr_ghci = addSpecsToGhcInfos ghci gs
    logEventStartM UpdateEvals
    evals' <- updateEvals curr_ghci lrs fc evals
    logEventEndM
    logEventStartM Synth
    synth_gs <- lift . lift . lift $ synthesize con iter curr_ghci lrs evals' meas_ex (unionFC max_fc fc) ut blk_mdls (concat below_sf) sf
    logEventEndM

    liftIO $ do
        putStrLn "-------"
        putStrLn $ "lengths = " ++ show (HM.map (length . nub) (blockedHashMap blk_mdls))
        putStrLn "-------"

    case synth_gs of
        SynthEnv envN sz smt_mdl blk_mdls' -> do
            let gs' = unionDroppingGS gs envN
                ghci' = addSpecsToGhcInfos ghci gs'
            liftIO $ do
                putStrLn "inferenceB"
                putStrLn $ "fs = " ++ show fs
                putStrLn $ "init gs' = " ++ show gs'

            logEventStartM Verify
            res <- tryToVerify ghci'
            logEventEndM
            let res' = filterNamesTo fs res

            case res' of
                Safe -> return $ (Env gs' fc max_fc meas_ex, evals')
                Unsafe bad -> do
                    inf_con <- infConfigM
                    ref <- tryToGen (nub bad) ((emptyFC, emptyBlockedModels), emptyFC)
                              (\(fc1, bm1) (fc2, bm2) -> (fc1 `unionFC` fc2, bm1 `unionBlockedModels` bm2))
                              unionFC
                              [ (\n -> do
                                    logEventStartM (InfSE n)
                                    return $ Right (Nothing, emptyFC))
                              , refineUnsafe ghci m_modname lrs gs'
                              , if use_level_dec inf_con then searchBelowLevel ghci m_modname lrs res sf gs' else genEmp
                              , if use_negated_models inf_con then adjModel lrs sz smt_mdl else incrCExAndTime ]
                              logEventEndM

                    case ref of
                        Left cex -> return $ (CEx cex, evals')
                        Right ((viol_fc, new_blk_mdls), no_viol_fc) -> do
                            let fc' = viol_fc `unionFC` no_viol_fc
                                blk_mdls'' = blk_mdls' `unionBlockedModels` new_blk_mdls
                            liftIO $ putStrLn "Before genMeasureExs"
                            logEventStartM UpdateMeasures
                            meas_ex' <- lift . lift . lift $ updateMeasureExs meas_ex lrs ghci fc'
                            logEventEndM
                            liftIO $ putStrLn "After genMeasureExs"

                            inferenceB con AfterFirstRound ghci m_modname lrs nls evals' meas_ex' gs (unionFC fc fc') max_fc ut blk_mdls''

                Crash e1 e2 -> error $ "inferenceB: LiquidHaskell crashed" ++ "\n" ++ show e1 ++ "\n" ++ e2
        SynthFail sf_fc -> do
            liftIO . T.putStrLn $ "synthfail fc = " <> (printFCs lrs sf_fc)
            incrBackTrackLog
            return $ (Raise meas_ex fc (unionFC max_fc sf_fc), evals')

tryToGen :: Monad m =>
            [n] -- ^ A list of values to produce results for
         -> (r, ex) -- ^ A default result, in case none of the strategies work, or we are passed an empty [n]
         -> (r -> r -> r) -- ^ Some way of combining results
         -> (ex -> ex -> ex) -- ^ Some way of joining extra results
         -> [n -> m (Either err (Maybe r, ex))] -- ^ A list of strategies, in order, to try and produce a result
         -> m () -- ^ A monadic action to run after each n is processed
         -> m (Either err (r, ex))
tryToGen [] def _ _ _ _= return $ Right def
tryToGen (n:ns) def join_r join_ex fs final_m = do
    gen1 <- tryToGen' n def join_ex fs
    final_m
    case gen1 of
        Left err -> return $ Left err
        Right (r1, ex1) -> do
            gen2 <- tryToGen ns def join_r join_ex fs final_m
            case gen2 of
                Left err -> return $ Left err
                Right (r2, ex2) -> return $ Right (r1 `join_r` r2, ex1 `join_ex` ex2) 

tryToGen' :: Monad m =>
             n
          -> (r, ex)
          -> (ex -> ex -> ex)
          -> [n -> m (Either err (Maybe r, ex))]
          -> m (Either err (r, ex))
tryToGen' _ def _ [] = return $ Right (def)
tryToGen' n def join_ex (f:fs) = do
    gen1 <- f n
    case gen1 of
        Left err -> return $ Left err
        Right (Just r, ex) -> return $ Right (r, ex)
        Right (Nothing, ex1) -> do
            gen2 <- tryToGen' n def join_ex fs
            case gen2 of
                Left err -> return $ Left err
                Right (r, ex2) -> return $ Right (r, ex1 `join_ex` ex2)

genEmp :: Monad m => Name -> InfStack m (Either [CounterExample] (Maybe a, FuncConstraints))
genEmp _ = return $ Right (Nothing, emptyFC)

refineUnsafeAll :: MonadIO m => 
                    [GhcInfo]
                -> Maybe T.Text
                -> LiquidReadyState
                -> GeneratedSpecs
                -> [Name]
                -> InfStack m (Either [CounterExample] (Maybe FuncConstraints, FuncConstraints))
refineUnsafeAll ghci m_modname lrs gs bad = do
    res <- mapM (refineUnsafe ghci m_modname lrs gs) (nub bad)

    case fmap unzip $ partitionEithers res of
        (cex@(_:_), _) -> return . Left $ concat cex
        ([], (new_fcs, no_viol_fcs)) -> 
            let
                new_fcs' = unionsFC . map fst $ catMaybes new_fcs
            in
            return . Right $ (if nullFC new_fcs' then Nothing else Just new_fcs', unionsFC no_viol_fcs)

refineUnsafe :: MonadIO m => 
                [GhcInfo]
             -> Maybe T.Text
             -> LiquidReadyState
             -> GeneratedSpecs
             -> Name
             -> InfStack m (Either [CounterExample] (Maybe (FuncConstraints, BlockedModels), FuncConstraints))
refineUnsafe ghci m_modname lrs gs bad = do
    let merged_se_ghci = addSpecsToGhcInfos ghci gs

    (res, no_viol) <- genNewConstraints merged_se_ghci m_modname lrs (nameOcc bad)

    liftIO $ do
        putStrLn $ "--- Generated Counterexamples and Constraints for " ++ show bad ++ " ---"
        putStrLn "res = "
        printCE (T.state $ lr_state lrs) res

    let res' = filter (not . hasAbstractedArgError) res

    -- Either converts counterexamples to FuncConstraints, or returns them as errors to
    -- show to the user.
    new_fc <- checkNewConstraints ghci lrs res'

    case new_fc of
        Left cex -> return $ Left cex
        Right new_fc' -> do
            liftIO . T.putStrLn $ "new_fc' = " <> printFCs lrs new_fc'
            return $ Right (if nullFC new_fc'
                                    then Nothing
                                    else Just (new_fc', emptyBlockedModels), fromListFC no_viol)

searchBelowLevel :: MonadIO m =>
                    [GhcInfo]
                 -> Maybe T.Text
                 -> LiquidReadyState
                 -> VerifyResult Name
                 -> [Name]
                 -> GeneratedSpecs
                 -> Name
                 -> InfStack m (Either [CounterExample] (Maybe (FuncConstraints, BlockedModels), FuncConstraints))
searchBelowLevel ghci m_modname lrs verify_res lev_below gs bad = do
    incrSearchBelowLog
    let called_by_res = calledByFunc lrs bad
    case filterNamesTo called_by_res $ filterNamesTo lev_below verify_res of
        Unsafe bad_sf -> do
            liftIO $ putStrLn "About to run second run of CEx generation"
            ref_sf <- withConfigs (limitedCounterfactual $ namesGS gs) $ refineUnsafeAll ghci m_modname lrs gs bad_sf
            case ref_sf of
                Left cex -> return $ Left cex
                Right (viol_fc_sf, no_viol_fc_sf) ->
                    return $ Right (fmap (, emptyBlockedModels) viol_fc_sf, no_viol_fc_sf)
        Safe -> return $ Right (Nothing, emptyFC)
        Crash _ _ -> error "inferenceB: LiquidHaskell crashed"

adjModel :: MonadIO m => 
            LiquidReadyState
         -> Size
         -> SMTModel
         -> Name
         -> InfStack m (Either a (Maybe (FuncConstraints, BlockedModels), FuncConstraints))
adjModel lrs sz smt_mdl n = do
    incrNegatedModelLog
    liftIO $ putStrLn "adjModel repeated_fc"
    let clls = calledByFunc lrs n
        blk_mdls' = insertBlockedModel sz (MNOnly (n:clls)) smt_mdl emptyBlockedModels

    liftIO . putStrLn $ "blocked models = " ++ show blk_mdls'

    _ <- incrCExAndTime n
    return . Right $ (Just (emptyFC, blk_mdls'), emptyFC)

incrCExAndTime :: Monad m => Name -> InfStack m (Either a (Maybe b, FuncConstraints))
incrCExAndTime (Name n m _ _) = do
    incrMaxCExI (n, m)
    incrMaxTimeI (n, m)
    incrMaxCFI (n, m)
    return $ Right (Nothing, emptyFC) 

calledByFunc :: LiquidReadyState -> Name -> [Name]
calledByFunc lrs n = 
    let
        eenv = expr_env . G2LH.state $ lr_state lrs
    in
    map zeroOutUnq
        . filter (isJust . flip E.lookup eenv)
        . maybe [] id
        . fmap varNames
        . fmap snd
        $ E.lookupNameMod (nameOcc n) (nameModule n) eenv

filterNamesTo ::  [Name] -> VerifyResult Name -> VerifyResult Name
filterNamesTo ns (Unsafe unsafe) = 
    case filter (\n -> toOccMod n `elem` ns_nm) unsafe of
        [] -> Safe
        unsafe' -> do
          Unsafe unsafe'
    where
        ns_nm = map toOccMod ns
        toOccMod (Name n m _ _) = (n, m)
filterNamesTo _ vr = vr

limitedCounterfactual :: [Name] -> Configs -> Configs
limitedCounterfactual ns cfgs@(Configs { g2lh_config = g2lh_c }) =
    cfgs { g2lh_config = g2lh_c { counterfactual = Counterfactual
                                                 . CFOnly
                                                 . S.fromList
                                                 $ map (\(Name n m _ _) -> (n, m)) ns } }

genNewConstraints :: MonadIO m => 
                     [GhcInfo]
                  -> Maybe T.Text
                  -> LiquidReadyState
                  -> T.Text
                  -> InfStack m ([CounterExample], [FuncConstraint])
genNewConstraints ghci m lrs n = do
    liftIO . putStrLn $ "Generating constraints for " ++ T.unpack n
    infconfig <- infConfigM

    ((exec_res, _), i) <- runLHInferenceCore n m lrs ghci
    let (exec_res', no_viol) = partition (true_assert . final_state) exec_res
        
        allCCons = noAbsStatesToCons i $ exec_res' ++ if use_extra_fcs infconfig then no_viol else []
    return $ (filter (not . hasPreArgError) $ map lhStateToCE exec_res', allCCons)

getCEx :: MonadIO m =>
          [GhcInfo]
       -> Maybe T.Text
       -> LiquidReadyState
       -> GeneratedSpecs
       -> [Name]
       -> InfStack m (Either [CounterExample] FuncConstraints)
getCEx ghci m_modname lrs gs bad = do
    let merged_se_ghci = addSpecsToGhcInfos ghci gs

    liftIO $ mapM_ (print . getTySigs) merged_se_ghci

    let bad' = nub $ map nameOcc bad

    res <- mapM (checkForCEx merged_se_ghci m_modname lrs) bad'

    liftIO $ do
        putStrLn $ "getCEx res = "
        printCE (T.state $ lr_state lrs) $ concat res

    let res' = concat res

    -- Either converts counterexamples to FuncConstraints, or returns them as errors to
    -- show to the user.
    new_fc <- checkNewConstraints ghci lrs res'

    case new_fc of
        Left cex -> return $ Left cex
        Right new_fc' -> do
            liftIO . T.putStrLn $ "new_fc' = " <> printFCs lrs new_fc'
            return $ Right new_fc'

checkForCEx :: MonadIO m =>
               [GhcInfo]
            -> Maybe T.Text
            -> LiquidReadyState
            -> T.Text
            -> InfStack m [CounterExample]
checkForCEx ghci m lrs n = do
    liftIO . putStrLn $ "Checking CEx for " ++ T.unpack n
    ((exec_res, _), _) <- runLHCExSearch n m lrs ghci
    let exec_res' = filter (true_assert . final_state) exec_res
    return $ map lhStateToCE exec_res'

checkNewConstraints :: (InfConfigM m, MonadIO m) => [GhcInfo] -> LiquidReadyState -> [CounterExample] -> m (Either [CounterExample] FuncConstraints)
checkNewConstraints ghci lrs cexs = do
    infconfig <- infConfigM
    res <- mapM (cexsToBlockingFC lrs ghci) cexs
    res2 <- return . concat =<< mapM cexsToExtraFC cexs
    case lefts res of
        res'@(_:_) -> return . Left $ res'
        _ -> return . Right . unionsFC . map fromSingletonFC $ (rights res) ++ if use_extra_fcs infconfig then res2 else []

updateMeasureExs :: (InfConfigM m, ProgresserM m, MonadIO m) => MeasureExs -> LiquidReadyState -> [GhcInfo] -> FuncConstraints -> m MeasureExs
updateMeasureExs meas_ex lrs ghci fcs =
    let
        es = concatMap (\fc ->
                    let
                        clls = concatMap (\(mfc, hfc) -> mfc:hfc) $ allCalls fc
                        vls = concatMap (\c -> returns c:arguments c) clls 
                        ex_poly = concat . concatMap extractValues . concatMap (extractExprPolyBound (tyvar_env  . G2LH.state $ lr_state lrs))  $ vls
                    in
                    vls ++ ex_poly
                ) (toListFC fcs)
    in
    evalMeasures meas_ex lrs ghci es

synthesize :: (InfConfigM m, ProgresserM m, MonadIO m, SMTConverter con)
           => con -> Iteration -> [GhcInfo] -> LiquidReadyState -> Evals Bool -> MeasureExs
           -> FuncConstraints -> UnionedTypes -> BlockedModels -> [Name] -> [Name] -> m SynthRes
synthesize con iter ghci lrs evals meas_ex fc ut blk_mdls to_be for_funcs = do
    liaSynth con iter ghci lrs evals meas_ex fc ut blk_mdls to_be for_funcs

updateEvals :: (InfConfigM m, MonadIO m) => [GhcInfo] -> LiquidReadyState -> FuncConstraints -> Evals Bool -> m (Evals Bool)
updateEvals ghci lrs fc evals = do
    let cs = allCallsFC fc

    liftIO $ putStrLn "Before check func calls"
    evals' <- preEvals evals lrs ghci cs
    liftIO $ putStrLn "After pre"
    evals'' <- postEvals evals' lrs ghci cs
    liftIO $ putStrLn "After check func calls"

    return evals''

-- | Converts counterexamples into constraints that block the current specification set
cexsToBlockingFC :: (InfConfigM m, MonadIO m) => LiquidReadyState -> [GhcInfo] -> CounterExample -> m (Either CounterExample FuncConstraint)
cexsToBlockingFC _ _ (DirectCounter dfc fcs@(_:_) higher)
    | (_:_, _) <- partition (hasArgError . abstract) fcs = undefined
    | isError (returns (abstract dfc)) = do
        infconfig <- infConfigM
        let fcs' = filter (\fc -> abstractedMod fc `S.member` modules infconfig) fcs

        let rhs = OrFC $ map (\(Abstracted { abstract = fc }) -> 
                        ImpliesFC (Call Pre fc higher) (NotFC (Call Post fc higher))) fcs'

        return . Right $ ImpliesFC (Call Pre (abstract dfc) higher) rhs
    | otherwise = do
        infconfig <- infConfigM
        let fcs' = filter (\fc -> abstractedMod fc `S.member` modules infconfig) fcs

        let lhs = AndFC [Call Pre (abstract dfc) higher, NotFC (Call Post (abstract dfc) higher)]
            rhs = OrFC $ map (\(Abstracted { abstract = fc }) -> 
                        ImpliesFC (Call Pre fc higher) (NotFC (Call Post fc higher))) fcs'

        if not . null $ fcs'
            then return . Right $ ImpliesFC lhs rhs
            else error "cexsToBlockingFC: Unhandled"
cexsToBlockingFC _ _ (CallsCounter dfc cfc fcs@(_:_) higher)
    | (_:_, _) <- partition (hasArgError . abstract) fcs = undefined
    | isError (returns (abstract cfc)) = do
        infconfig <- infConfigM
        let fcs' = filter (\fc -> abstractedMod fc `S.member` modules infconfig) fcs

        let lhs = Call Pre (abstract dfc) higher
            rhs = OrFC $ map (\(Abstracted { abstract = fc }) -> 
                                ImpliesFC (Call Pre fc higher) (NotFC (Call Post fc higher))) fcs'

        if not . null $ fcs' 
            then return . Right $ ImpliesFC lhs rhs
            else error "cexsToBlockingFC: Should be unreachable! Non-refinable function abstracted!"    

    | otherwise = do
        infconfig <- infConfigM
        let fcs' = filter (\fc -> abstractedMod fc `S.member` modules infconfig) fcs

        let lhs = AndFC [Call Pre (abstract dfc) higher, NotFC (Call Pre (abstract cfc) higher)]
            rhs = OrFC $ map (\(Abstracted { abstract = fc }) -> 
                                ImpliesFC (Call Pre fc higher) (NotFC (Call Post fc higher))) fcs'

        if not . null $ fcs' 
            then return . Right $ ImpliesFC lhs rhs
            else error "cexsToBlockingFC: Should be unreachable! Non-refinable function abstracted!"    
cexsToBlockingFC lrs ghci cex@(DirectCounter dfc [] higher)
    | isError (returns (real dfc)) = do
        if isExported lrs (funcName (real dfc))
            then return . Left $ cex
            else return . Right . NotFC $ Call Pre (real dfc) higher
    | isExported lrs (funcName (real dfc)) = do
        post_ref <- checkPost ghci lrs (real dfc) higher
        case post_ref of
            True -> return $ Right (Call All (real dfc) higher)
            False -> return . Left $ cex
    | otherwise = return $ Right (Call All (real dfc) higher)
cexsToBlockingFC lrs ghci cex@(CallsCounter dfc cfc [] higher)
    | any isError (arguments (abstract cfc)) = do
        if
            | isExported lrs (funcName (real dfc))
            , isExported lrs (funcName (real cfc)) -> do
                called_pr <- checkPre ghci lrs (real cfc) higher -- TODO: Shouldn't be changing this?
                case called_pr of
                    True -> return . Right $ NotFC (Call Pre (real dfc) higher)
                    False -> return . Left $ cex
            | isExported lrs (funcName (real dfc)) -> do
                called_pr <- checkPre ghci lrs (real cfc) higher
                case called_pr of
                    True -> return . Right $ NotFC (Call Pre (real dfc) higher)
                    False -> return . Left $ cex
            | otherwise -> return . Right $ NotFC (Call Pre (real dfc) higher)
    | otherwise = do
        if
            | isExported lrs (funcName (real dfc))
            , isExported lrs (funcName (real cfc)) -> do
                called_pr <- checkPre ghci lrs (real cfc) higher -- TODO: Shouldn't be changing this?
                case called_pr of
                    True -> return . Right $ ImpliesFC (Call Pre (real dfc) higher) (Call Pre (real cfc) higher)
                    False -> return . Left $ cex
            | isExported lrs (funcName (real dfc)) -> do
                called_pr <- checkPre ghci lrs (real cfc) higher
                case called_pr of
                    True -> return . Right $ ImpliesFC (Call Pre (real dfc) higher) (Call Pre (real cfc) higher)
                    False -> return . Left $ cex
            | otherwise -> do
                return . Right $ ImpliesFC (Call Pre (real dfc) higher) (Call Pre (real cfc) higher)

-- Function constraints that don't block the current specification set, but which must be true
-- (i.e. the actual input and output for abstracted functions)
cexsToExtraFC :: InfConfigM m => CounterExample -> m [FuncConstraint]
cexsToExtraFC (DirectCounter dfc fcs@(_:_) higher) = do
    infconfig <- infConfigM
    let some_pre = ImpliesFC (Call Pre (real dfc) higher) $  OrFC (map (\fc -> Call Pre (real fc) higher) fcs)
        fcs' = filter (\fc -> abstractedMod fc `S.member` modules infconfig) fcs
    return $ some_pre:mapMaybe (realToMaybeFC higher) fcs'
cexsToExtraFC (CallsCounter dfc cfc fcs@(_:_) higher) = do
    infconfig <- infConfigM
    let some_pre = ImpliesFC (Call Pre (real dfc) higher) $  OrFC (map (\fc -> Call Pre (real fc) higher) fcs)
    let fcs' = filter (\fc -> abstractedMod fc `S.member` modules infconfig) fcs

    let pre_real = maybeToList $ (realToMaybeFC higher) cfc
        as = mapMaybe (realToMaybeFC higher) fcs'
        clls = if not . isError . returns . real $ cfc
                  then [Call All (real cfc) higher]
                  else []

    return $ some_pre:clls ++ pre_real ++ as
cexsToExtraFC (DirectCounter _ [] _) = return []
cexsToExtraFC (CallsCounter dfc cfc [] higher)
    | isError (returns (real dfc)) = return []
    | isError (returns (real cfc)) = return []
    | any isError (arguments (real cfc)) = return []
    | otherwise =
        let
            call_all_dfc = Call All (real dfc) higher
            call_all_cfc = Call All (real cfc) higher
            imp_fc = ImpliesFC (Call Pre (real dfc) higher) (Call Pre (real cfc) higher)
        in
        return $ [call_all_dfc, call_all_cfc, imp_fc]

noAbsStatesToCons :: Id -> [ExecRes AbstractedInfo] -> [FuncConstraint]
noAbsStatesToCons i = concatMap (noAbsStatesToCons' i) -- . filter (null . abs_calls . track . final_state)

noAbsStatesToCons' :: Id -> ExecRes AbstractedInfo -> [FuncConstraint]
noAbsStatesToCons' i@(Id (Name _ m _ _) _) er =
    let
        higher_calls = erHigherOrder er

        pre_s = lhStateToPreFC i er
        clls = filter (\fc -> nameModule (funcName fc) == m) 
             . map (switchName (idName i))
             . filter (not . hasArgError)
             . func_calls_in_real
             . init_call
             . track
             $ final_state er

        preCons = map (ImpliesFC pre_s . flip (Call Pre) higher_calls) clls
        -- A function may return error because it was passed an erroring higher order function.
        -- In this case, it would be incorrect to add a constraint that the function itself calls error.
        -- Thus, we simply get rid of constraints that call error. 
        callsCons = mapMaybe (\fc -> case isError (returns fc) of
                                      True -> Nothing -- NotFC (Call Pre fc)
                                      False -> Just (Call All fc higher_calls)) clls
        callsCons' = if hits_lib_err_in_real (init_call . track . final_state $ er)
                                    then []
                                    else callsCons
    in
    preCons ++ callsCons'

switchName :: Name -> FuncCall -> FuncCall
switchName n fc = if funcName fc == initiallyCalledFuncName then fc { funcName = n } else fc

--------------------------------------------------------------------

realToMaybeFC :: [HigherOrderFuncCall] -> Abstracted -> Maybe FuncConstraint
realToMaybeFC higher a@(Abstracted { real = fc }) 
    | hits_lib_err_in_real a = Nothing
    | isError (returns fc) = Just $ NotFC (Call Pre fc higher)
    | otherwise = Just $ ImpliesFC (Call Pre fc higher) (Call Post fc higher)

isExported :: LiquidReadyState -> Name -> Bool
isExported lrs (Name n m _ _) =
    (n, m) `elem` map (\(Name n' m' _ _) -> (n', m')) (exported_funcs (lr_binding lrs))

lhStateToPreFC :: Id -> ExecRes AbstractedInfo -> FuncConstraint
lhStateToPreFC i er@(ExecRes { conc_args = inArg
                             , conc_out = ex}) = Call Pre (FuncCall (idName i) inArg ex) (erHigherOrder er)

abstractedMod :: Abstracted -> Maybe T.Text
abstractedMod = nameModule . funcName . abstract

hasPreArgError :: CounterExample -> Bool
hasPreArgError (DirectCounter _ _ _) = False
hasPreArgError (CallsCounter _ calls_f _ _) = hasArgError $ real calls_f

hasAbstractedArgError :: CounterExample -> Bool
hasAbstractedArgError (DirectCounter _ as _) = any (hasArgError . real) as
hasAbstractedArgError (CallsCounter _ _ as _) = any (hasArgError . real) as

hasArgError :: FuncCall -> Bool
hasArgError = any isError . arguments

isError :: Expr -> Bool
isError (Prim Error _) = True
isError (Prim Undefined _) = True
isError _ = False

erHigherOrder :: ExecRes AbstractedInfo -> [HigherOrderFuncCall]
erHigherOrder = ai_higher_order_calls . track . final_state
