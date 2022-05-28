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
import G2.Liquid.ConvertCurrExpr
import G2.Liquid.Helpers
import G2.Liquid.Inference.Config
import G2.Liquid.Inference.FuncConstraint as FC
import G2.Liquid.Inference.G2Calls
import G2.Liquid.Inference.InfStack
import G2.Liquid.Inference.Initalization
import G2.Liquid.Inference.PolyRef
import G2.Liquid.Inference.Sygus
import G2.Liquid.Inference.GeneratedSpecs
import G2.Liquid.Inference.Verify
import G2.Liquid.Interface
import G2.Liquid.Types hiding (state)
import qualified G2.Liquid.Types as T
import qualified G2.Liquid.Types as G2LH
import G2.Solver
import G2.Translation

import Language.Haskell.Liquid.Types hiding (Config, cls, names, measures)
import Language.Haskell.Liquid.Types as LH

import Control.Monad.IO.Class 
import Control.Monad.Reader
import Data.Either
import qualified Data.HashSet as S
import qualified Data.HashMap.Lazy as HM
import Data.List
import Data.Maybe
import qualified Data.Text as T

import Debug.Trace

-- Run inference, with an extra, final check of correctness at the end.
-- Assuming inference is working correctly, this check should neve fail.
inferenceCheck :: InferenceConfig -> G2.Config -> [FilePath] -> [FilePath] -> [FilePath] -> IO (Either [CounterExample ConcAbsFuncCall] GeneratedSpecs)
inferenceCheck infconfig config proj fp lhlibs = do
    (ghci, lhconfig) <- getGHCI infconfig proj fp lhlibs
    (res, _, loops) <- inference' infconfig config lhconfig ghci proj fp lhlibs
    print $ loop_count loops
    print . sum . HM.elems $ loop_count loops
    print $ searched_below loops
    print $ negated_models loops
    case res of
        Right gs -> do
            check_res <- checkGSCorrect infconfig lhconfig ghci gs
            case check_res of
                Safe -> return res
                _ -> error "inferenceCheck: Check failed"
        _ -> return res

inference :: InferenceConfig -> G2.Config -> [FilePath] -> [FilePath] -> [FilePath] -> IO (Either [CounterExample ConcAbsFuncCall] GeneratedSpecs)
inference infconfig config proj fp lhlibs = do
    -- Initialize LiquidHaskell
    (ghci, lhconfig) <- getGHCI infconfig proj fp lhlibs
    (res, timer, _) <- inference' infconfig config lhconfig ghci proj fp lhlibs
    print . logToSecs . sumLog . getLog $ timer
    return res

inference' :: InferenceConfig
           -> G2.Config
           -> LH.Config
           -> [GhcInfo]
           -> [FilePath]
           -> [FilePath]
           -> [FilePath]
           -> IO (Either [CounterExample ConcAbsFuncCall] GeneratedSpecs, Timer (Event Name), Counters)
inference' infconfig config lhconfig ghci proj fp lhlibs = do
    mapM_ (print . getQualifiers) ghci

    (lrs, g2config', infconfig', main_mod) <- getInitState proj fp lhlibs ghci infconfig config
    let nls = getNameLevels main_mod lrs

    putStrLn $ "nls = " ++ show nls

    let configs = Configs { g2_config = g2config', lh_config = lhconfig, inf_config = infconfig'}
        prog = newProgress

    SomeSMTSolver solver <- getSMT g2config'
    let infL = iterativeInference solver ghci main_mod lrs nls HM.empty emptyGS emptyFC

    (res, ev_timer, lvl_timer, loops) <- runInfStack configs prog infL -- runProgresser (runConfigs (runTimer infL timer) configs) prog

    print . logToSecs . orderLogBySpeed . sumLog . getLog $ lvl_timer

    print . logToSecs . orderLogBySpeed . sumLog . mapLabels (mapEvent (nameOcc)) . getLog $ ev_timer
    print . logToSecs . orderLogBySpeed . sumLog . mapLabels (mapEvent (const ())) . getLog $ ev_timer
    return (res, ev_timer, loops)

getInitState :: [FilePath]
             -> [FilePath]
             -> [FilePath]
             -> [GhcInfo]
             -> InferenceConfig
             -> G2.Config
             -> IO (LiquidReadyState, G2.Config, InferenceConfig, Maybe T.Text)
getInitState proj fp lhlibs ghci infconfig config = do
    let g2config = config { mode = Liquid
                          , steps = 2000 }
        transConfig = simplTranslationConfig { simpl = False }
    (main_mod, exg2) <- translateLoaded proj fp lhlibs transConfig g2config

    let (lrs, g2config', infconfig') = initStateAndConfig exg2 main_mod g2config infconfig ghci
    return (lrs, g2config', infconfig', main_mod)

getNameLevels :: Maybe T.Text -> LiquidReadyState -> NameLevels
getNameLevels main_mod =
    filter (not . null)
       . map nub
       . map (filter (\(Name _ m _ _) -> m == main_mod))
       . nameLevels
       . getCallGraph
       . expr_env . G2LH.state . lr_state

data InferenceRes = CEx [CounterExample ConcAbsFuncCall]
                  | Env GeneratedSpecs
                        FuncConstraints
                        MaxSizeConstraints
                        MeasureExs
                        Size -- ^ The size that the synthesizer succeeded at
                        SMTModel -- ^ An SMTModel corresponding to the new specifications
                  | Raise MeasureExs
                          FuncConstraints -- ^ `FuncConstraints` corresponding to verification requirements
                          MaxSizeConstraints -- ^ `FuncConstraints` that might hold only due to the max synthesis size
                          Interpolant -- ^ Newly generated `FuncConstraints` that block going down a bad path
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
                   -> InfStack m (Either [CounterExample ConcAbsFuncCall] GeneratedSpecs)
iterativeInference con ghci m_modname lrs nls meas_ex gs fc = do
    res <- inferenceL con ghci m_modname lrs nls emptyEvals meas_ex gs fc emptyFC emptyBlockedModels
    case res of
        CEx cex -> return $ Left cex
        Env n_gs _ _ _ _ _ -> return $ Right n_gs
        Raise _ r_fc _ _ -> do
            incrMaxDepthI
            -- We might be missing some internal GHC types from our deep_seq walkers
            -- We filter them out to avoid an error
            let eenv = expr_env . G2LH.state $ lr_state lrs
                chck = filter (\n -> 
                                  case E.lookup n eenv of
                                      Just e -> isJust $ 
                                              mkStrict_maybe 
                                              (deepseq_walkers $ lr_binding lrs) 
                                              (Var (Id (Name "" Nothing 0 Nothing) (returnType e)))
                                      Nothing -> False) (head nls)
            liftIO . putStrLn $ "head nls =  " ++ show (head nls)
            liftIO . putStrLn $ "iterativeInference check =  " ++ show chck

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
                    iterativeInference con ghci m_modname lrs nls r_meas_ex' gs (unionFC fc' r_fc)


inferenceL :: (MonadIO m, SMTConverter con)
           => con
           -> [GhcInfo]
           -> Maybe T.Text
           -> LiquidReadyState
           -> NameLevels
           -> Evals Bool
           -> MeasureExs
           -> GeneratedSpecs
           -> FuncConstraints
           -> MaxSizeConstraints
           -> BlockedModels
           -> InfStack m InferenceRes
inferenceL con ghci m_modname lrs nls evals meas_ex senv fc max_fc blk_mdls = do
    let (fs, sf, below_sf) = case nls of
                        (fs_:sf_:be) -> (fs_, sf_, be)
                        ([fs_])-> (fs_, [], [])
                        [] -> ([], [], [])

    startLevelTimer (case nls of fs_:_ -> fs_; [] -> [])
    (resAtL, evals') <- inferenceB con ghci m_modname lrs nls evals meas_ex senv fc max_fc blk_mdls
    endLevelTimer

    liftIO $ do
        putStrLn "-------"
        putStrLn $ "lengths = " ++ show (HM.map (length . nub) (blockedHashMap blk_mdls))
        putStrLn "-------"

    case resAtL of
        Env senv' n_fc n_mfc meas_ex' sz smt_mdl -> 
            case nls of
                [] -> return resAtL
                (_:nls') -> do
                    liftIO $ putStrLn "Down a level!"
                    let evals'' = foldr deleteEvalsForFunc evals' sf
                    inf_res <- inferenceL con ghci m_modname lrs nls' evals'' meas_ex' senv' (unionFC fc n_fc) (unionFC max_fc n_mfc) emptyBlockedModels
                    case inf_res of
                        Raise r_meas_ex r_fc r_max_fc interp -> do
                            liftIO $ putStrLn "Up a level!"
                            
                            case nullFC interp of
                                True -> do
                                    new_blk_mdls <- getBlockedModel lrs sz smt_mdl
                                    inferenceL con ghci m_modname lrs nls evals' r_meas_ex senv r_fc r_max_fc (new_blk_mdls `unionBlockedModels` blk_mdls)
                                False -> inferenceL con ghci m_modname lrs nls evals' r_meas_ex senv r_fc (r_max_fc `unionFC` interp) blk_mdls
                        _ -> return inf_res
        _ -> return resAtL

inferenceB :: (MonadIO m, SMTConverter con)
           => con
           -> [GhcInfo]
           -> Maybe T.Text
           -> LiquidReadyState
           -> NameLevels
           -> Evals Bool
           -> MeasureExs
           -> GeneratedSpecs
           -> FuncConstraints
           -> MaxSizeConstraints
           -> BlockedModels
           -> InfStack m (InferenceRes, Evals Bool)
inferenceB con ghci m_modname lrs nls evals meas_ex gs fc max_fc blk_mdls = do
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
    synth_gs <- lift . lift . lift $ synthesize con curr_ghci lrs evals' meas_ex (unionFC max_fc fc) blk_mdls (concat below_sf) sf
    logEventEndM

    liftIO $ do
        putStrLn "-------"
        putStrLn $ "lengths = " ++ show (HM.map (length . nub) (blockedHashMap blk_mdls))
        putStrLn "-------"

    case synth_gs of
        SynthEnv envN sz smt_mdl blk_mdls' synth_fc sy_evals sy_meas_ex -> do
            let gs' = unionDroppingGS gs envN
                ghci' = addSpecsToGhcInfos ghci gs'

                fc' = fc `unionFC` synth_fc
            liftIO $ do
                putStrLn "inferenceB"
                putStrLn $ "fs = " ++ show fs
                putStrLn $ "init gs' = " ++ show gs'

            logEventStartM Verify
            res <- tryToVerify ghci'
            logEventEndM
            let res' = filterNamesTo fs res
            
            case res' of
                Safe -> return $ (Env gs' fc' max_fc sy_meas_ex sz smt_mdl, sy_evals)
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
                        Left cex -> return $ (CEx cex, sy_evals)
                        Right ((viol_fc, new_blk_mdls), no_viol_fc) -> do
                            let viol_no_viol_fc = viol_fc `unionFC` no_viol_fc
                                blk_mdls'' = blk_mdls' `unionBlockedModels` new_blk_mdls
                            liftIO $ putStrLn "Before genMeasureExs"
                            logEventStartM UpdateMeasures
                            meas_ex' <- lift . lift . lift $ updateMeasureExs sy_meas_ex lrs ghci viol_no_viol_fc
                            logEventEndM
                            liftIO $ putStrLn "After genMeasureExs"

                            inferenceB con ghci m_modname lrs nls sy_evals meas_ex' gs (fc' `unionFC` viol_no_viol_fc) max_fc blk_mdls''

                Crash e1 e2 -> error $ "inferenceB: LiquidHaskell crashed" ++ "\n" ++ show e1 ++ "\n" ++ e2
        SynthFail sf_fc | otherwise -> return $ (Raise meas_ex fc max_fc sf_fc, evals')

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

genEmp :: Monad m => Name -> InfStack m (Either [CounterExample ConcAbsFuncCall] (Maybe a, FuncConstraints))
genEmp _ = return $ Right (Nothing, emptyFC)

refineUnsafeAll :: MonadIO m => 
                    [GhcInfo]
                -> Maybe T.Text
                -> LiquidReadyState
                -> GeneratedSpecs
                -> [Name]
                -> InfStack m (Either [CounterExample ConcAbsFuncCall] (Maybe FuncConstraints, FuncConstraints))
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
             -> InfStack m (Either [CounterExample ConcAbsFuncCall] (Maybe (FuncConstraints, BlockedModels), FuncConstraints))
refineUnsafe ghci m_modname lrs gs bad = do
    let merged_se_ghci = addSpecsToGhcInfos ghci gs

    liftIO $ mapM_ (print . getTySigs) merged_se_ghci

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
            liftIO . putStrLn $ "new conc fc = " ++ printConcFCs new_fc'
            liftIO . putStrLn $ "new abs fc = " ++ printAbsFCs new_fc'
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
                 -> InfStack m (Either [CounterExample ConcAbsFuncCall] (Maybe (FuncConstraints, BlockedModels), FuncConstraints))
searchBelowLevel ghci m_modname lrs verify_res lev_below gs bad = do
    incrSearchBelowLog
    let called_by_res = calledByFunc lrs bad
    case filterNamesTo called_by_res $ filterNamesTo lev_below verify_res of
        Unsafe bad_sf -> do
            liftIO $ putStrLn "About to run second run of CEx generation"
            ref_sf <- withConfigs noCounterfactual $ refineUnsafeAll ghci m_modname lrs gs bad_sf
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

getBlockedModel :: MonadIO m => LiquidReadyState -> Size -> SMTModel -> InfStack m BlockedModels
getBlockedModel lrs sz smt_mdl = do
    incrNegatedModelLog
    liftIO $ putStrLn "getBlockedModel"
    let blk_mdls' = insertBlockedModel sz MNAll smt_mdl emptyBlockedModels

    liftIO . putStrLn $ "blocked models = " ++ show blk_mdls'
    return blk_mdls'

incrCExAndTime :: Monad m => Name -> InfStack m (Either a (Maybe b, FuncConstraints))
incrCExAndTime (Name n m _ _) = do
    incrMaxCExI (n, m)
    incrMaxTimeI (n, m)
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

noCounterfactual :: Configs -> Configs
noCounterfactual cfgs@(Configs { g2_config = g2_c }) = cfgs { g2_config = g2_c { counterfactual = NotCounterfactual } }

genNewConstraints :: MonadIO m => 
                     [GhcInfo]
                  -> Maybe T.Text
                  -> LiquidReadyState
                  -> T.Text
                  -> InfStack m ([CounterExample ConcAbsFuncCall], [FuncConstraint])
genNewConstraints ghci m lrs n = do
    liftIO . putStrLn $ "Generating constraints for " ++ T.unpack n
    infconfig <- infConfigM

    ((exec_res, _), i) <- runLHInferenceCore n m lrs ghci
    let (exec_res', no_viol) = partition (true_assert . final_state . fst) exec_res
        
        allCCons = noAbsStatesToCons i
                 -- . map (uncurry toConcState)
                 $ exec_res' ++ if use_extra_fcs infconfig then no_viol else []
    return $ (filter (not . hasPreArgError) $ map (uncurry lhStateToCE) exec_res', allCCons)

getCEx :: MonadIO m =>
          [GhcInfo]
       -> Maybe T.Text
       -> LiquidReadyState
       -> GeneratedSpecs
       -> [Name]
       -> InfStack m (Either [CounterExample ConcAbsFuncCall] FuncConstraints)
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
            liftIO . putStrLn $ "new_fc' = " ++ printConcFCs new_fc'
            return $ Right new_fc'

checkForCEx :: MonadIO m =>
               [GhcInfo]
            -> Maybe T.Text
            -> LiquidReadyState
            -> T.Text
            -> InfStack m [CounterExample ConcAbsFuncCall]
checkForCEx ghci m lrs n = do
    liftIO . putStrLn $ "Checking CEx for " ++ T.unpack n
    ((exec_res, _), _) <- runLHCExSearch n m lrs ghci
    let exec_res' = filter (true_assert . final_state . fst) exec_res
    return $ map (uncurry lhStateToCE) exec_res'

checkNewConstraints :: (InfConfigM m, MonadIO m) => [GhcInfo] -> LiquidReadyState -> [CounterExample ConcAbsFuncCall] -> m (Either [CounterExample ConcAbsFuncCall] FuncConstraints)
checkNewConstraints ghci lrs cexs = do
    infconfig <- infConfigM
    res <- mapM (cexsToBlockingFC lrs ghci) cexs
    res2 <- return . concat =<< mapM cexsToExtraFC cexs
    case lefts res of
        res'@(_:_) -> return . Left $ res'
        _ -> return . Right . unionsFC . map fromSingletonFC $ (rights res) ++ if use_extra_fcs infconfig then res2 else []

synthesize :: (InfConfigM m, ProgresserM m, MonadIO m, SMTConverter con)
           => con -> [GhcInfo] -> LiquidReadyState -> Evals Bool -> MeasureExs
           -> FuncConstraints -> BlockedModels -> [Name] -> [Name] -> m SynthRes
synthesize con ghci lrs evals meas_ex fc blk_mdls to_be for_funcs = do
    liftIO . putStrLn $ "all fc = " ++ printConcFCs fc
    liaSynth con ghci lrs evals meas_ex fc blk_mdls to_be for_funcs

-- | Converts counterexamples into constraints that block the current specification set
cexsToBlockingFC :: (InfConfigM m, MonadIO m) => LiquidReadyState -> [GhcInfo] -> CounterExample ConcAbsFuncCall -> m (Either (CounterExample ConcAbsFuncCall) FuncConstraint)
cexsToBlockingFC _ _ (DirectCounter dfc fcs@(_:_))
    | (_:_, _) <- partition (hasArgError . conc_fcall . abstract) fcs = undefined
    | isError (returns . conc_fcall $ abstract dfc) = do
        infconfig <- infConfigM
        let fcs' = filter (\fc -> abstractedMod fc `S.member` modules infconfig) fcs

        let rhs = OrFC $ map (\(Abstracted { abstract = fc }) -> 
                        ImpliesFC (Call Pre fc) (NotFC (Call Post fc))) fcs'

        return . Right $ ImpliesFC (Call Pre (abstract dfc)) rhs
    | otherwise = do
        infconfig <- infConfigM
        let fcs' = filter (\fc -> abstractedMod fc `S.member` modules infconfig) fcs

        let lhs = AndFC [Call Pre (abstract dfc), NotFC (Call Post (abstract dfc))]
            rhs = OrFC $ map (\(Abstracted { abstract = fc }) -> 
                        ImpliesFC (Call Pre fc) (NotFC (Call Post fc))) fcs'

        if not . null $ fcs'
            then return . Right $ ImpliesFC lhs rhs
            else error "cexsToBlockingFC: Unhandled"
cexsToBlockingFC _ _ (CallsCounter dfc cfc fcs@(_:_))
    | (_:_, _) <- partition (hasArgError . conc_fcall . abstract) fcs = undefined
    | isError (returns . conc_fcall $ abstract cfc) = do
        infconfig <- infConfigM
        let fcs' = filter (\fc -> abstractedMod fc `S.member` modules infconfig) fcs

        let lhs = Call Pre (abstract dfc)
            rhs = OrFC $ map (\(Abstracted { abstract = fc }) -> 
                                ImpliesFC (Call Pre fc) (NotFC (Call Post fc))) fcs'

        if not . null $ fcs' 
            then return . Right $ ImpliesFC lhs rhs
            else error "cexsToBlockingFC: Should be unreachable! Non-refinable function abstracted!"    

    | otherwise = do
        infconfig <- infConfigM
        let fcs' = filter (\fc -> abstractedMod fc `S.member` modules infconfig) fcs

        let lhs = AndFC [Call Pre (abstract dfc), NotFC (Call Pre (abstract cfc))]
            rhs = OrFC $ map (\(Abstracted { abstract = fc }) -> 
                                ImpliesFC (Call Pre fc) (NotFC (Call Post fc))) fcs'

        if not . null $ fcs' 
            then return . Right $ ImpliesFC lhs rhs
            else error "cexsToBlockingFC: Should be unreachable! Non-refinable function abstracted!"    
cexsToBlockingFC lrs ghci cex@(DirectCounter dfc [])
    | isError (returns . conc_fcall . real $ dfc) = do
        if isExported lrs (funcName . conc_fcall . real $ dfc)
            then return . Left $ cex
            else return . Right . NotFC $ Call Pre (real dfc)
    | isExported lrs (funcName . conc_fcall . real $ dfc) = do
        post_ref <- checkPost ghci lrs (conc_fcall $ real dfc)
        case post_ref of
            True -> return $ Right (Call All (real dfc))
            False -> return . Left $ cex
    | otherwise = return $ Right (Call All (real dfc))
cexsToBlockingFC lrs ghci cex@(CallsCounter dfc cfc [])
    | any isError (arguments . conc_fcall . abstract $ cfc) = do
        if
            | isExported lrs (funcName . conc_fcall . real $ dfc)
            , isExported lrs (funcName . conc_fcall . real $ cfc) -> do
                called_pr <- checkPre ghci lrs (conc_fcall $ real cfc) -- TODO: Shouldn't be changing this?
                case called_pr of
                    True -> return . Right $ NotFC (Call Pre (real dfc))
                    False -> return . Left $ cex
            | isExported lrs (funcName . conc_fcall . real $ dfc) -> do
                called_pr <- checkPre ghci lrs (conc_fcall $ real cfc)
                case called_pr of
                    True -> return . Right $ NotFC (Call Pre (real dfc))
                    False -> return . Left $ cex
            | otherwise -> return . Right $ NotFC (Call Pre (real dfc))
    | otherwise = do
        if
            | isExported lrs (funcName . conc_fcall . real $ dfc)
            , isExported lrs (funcName . conc_fcall . real $ cfc) -> do
                called_pr <- checkPre ghci lrs (conc_fcall $ real cfc) -- TODO: Shouldn't be changing this?
                case called_pr of
                    True -> return . Right $ ImpliesFC (Call Pre (real dfc)) (Call Pre (real cfc))
                    False -> return . Left $ cex
            | isExported lrs (funcName . conc_fcall . real $ dfc) -> do
                called_pr <- checkPre ghci lrs (conc_fcall $ real cfc)
                case called_pr of
                    True -> return . Right $ ImpliesFC (Call Pre (real dfc)) (Call Pre (real cfc))
                    False -> return . Left $ cex
            | otherwise -> do
                return . Right $ ImpliesFC (Call Pre (real dfc)) (Call Pre (real cfc))

-- Function constraints that don't block the current specification set, but which must be true
-- (i.e. the actual input and output for abstracted functions)
cexsToExtraFC :: InfConfigM m => CounterExample ConcAbsFuncCall -> m [FuncConstraint]
cexsToExtraFC (DirectCounter dfc fcs@(_:_)) = do
    infconfig <- infConfigM
    let some_pre = ImpliesFC (Call Pre $ real dfc) $  OrFC (map (\fc -> Call Pre (real fc)) fcs)
        fcs' = filter (\fc -> abstractedMod fc `S.member` modules infconfig) fcs
    return $ some_pre:mapMaybe realToMaybeFC fcs'
cexsToExtraFC (CallsCounter dfc cfc fcs@(_:_)) = do
    infconfig <- infConfigM
    let some_pre = ImpliesFC (Call Pre $ real dfc) $  OrFC (map (\fc -> Call Pre (real fc)) fcs)
    let fcs' = filter (\fc -> abstractedMod fc `S.member` modules infconfig) fcs

    let pre_real = maybeToList $ realToMaybeFC cfc
        as = mapMaybe realToMaybeFC fcs'
        clls = if not . isError . returns . conc_fcall . real $ cfc
                  then [Call All $ real cfc]
                  else []

    return $ some_pre:clls ++ pre_real ++ as
cexsToExtraFC (DirectCounter _ []) = return []
cexsToExtraFC (CallsCounter dfc cfc [])
    | isError (returns . conc_fcall . real $ dfc) = return []
    | isError (returns . conc_fcall . real $ cfc) = return []
    | any isError (arguments . conc_fcall . real $ cfc) = return []
    | otherwise =
        let
            call_all_dfc = Call All (real dfc)
            call_all_cfc = Call All (real cfc)
            imp_fc = ImpliesFC (Call Pre $ real dfc) (Call Pre $ real cfc)
        in
        return $ [call_all_dfc, call_all_cfc, imp_fc]

noAbsStatesToCons :: Id -> [(ExecRes (AbstractedInfo AbsFuncCall), Model)] -> [FuncConstraint]
noAbsStatesToCons i = concatMap (uncurry (noAbsStatesToCons' i)) -- . filter (null . abs_calls . track . final_state)

noAbsStatesToCons' :: Id -> ExecRes (AbstractedInfo AbsFuncCall) -> Model -> [FuncConstraint]
noAbsStatesToCons' i@(Id (Name _ n_md _ _) _) er m =
    let
        conc_er = toConcState er m

        pre_s = lhStateToPreFC i er m
        clls = filter (\fc -> nameModule (caFuncName fc) == n_md) 
             . map (switchName (idName i))
             . filter (not . hasArgError . conc_fcall)
             . func_calls_in_real
             . init_call
             . track
             $ final_state conc_er

        preCons = map (ImpliesFC pre_s . Call Pre) clls
        -- A function may return error because it was passed an erroring higher order function.
        -- In this case, it would be incorrect to add a constraint that the function itself calls error.
        -- Thus, we simply get rid of constraints that call error. 
        callsCons = mapMaybe (\fc -> case isError . returns . conc_fcall $ fc of
                                      True -> Nothing -- NotFC (Call Pre fc)
                                      False -> Just (Call All fc)) clls
        callsCons' = if hits_lib_err_in_real (init_call . track . final_state $ conc_er)
                                    then []
                                    else callsCons
    in
    preCons ++ callsCons'

switchName :: Name -> ConcAbsFuncCall -> ConcAbsFuncCall
switchName n fc@(CAFuncCall { conc_fcall = cc, abs_fcall = ac@(AbsFuncCall { fcall = fac }) }) =
    if caFuncName fc == initiallyCalledFuncName
        then fc { conc_fcall = cc { funcName = n }
                , abs_fcall = ac { fcall = fac { funcName = n } } }
        else fc

--------------------------------------------------------------------

realToMaybeFC :: Abstracted ConcAbsFuncCall -> Maybe FuncConstraint
realToMaybeFC a@(Abstracted { real = fc }) 
    | hits_lib_err_in_real a = Nothing
    | isError . returns . conc_fcall $ fc = Just $ NotFC (Call Pre fc)
    | otherwise = Just $ ImpliesFC (Call Pre fc) (Call Post fc)

isExported :: LiquidReadyState -> Name -> Bool
isExported lrs (Name n m _ _) =
    (n, m) `elem` map (\(Name n' m' _ _) -> (n', m')) (exported_funcs (lr_binding lrs))

lhStateToPreFC :: Id -> ExecRes (AbstractedInfo AbsFuncCall) -> Model -> FuncConstraint
lhStateToPreFC i er@(ExecRes { final_state = a_s
                             , conc_args = a_inArg
                             , conc_out = a_out}) m =
    let
        ExecRes { final_state = c_s
                , conc_args = c_inArg
                , conc_out = c_out} = toConcState er m

        acall = mkAbsFuncCall a_s $ FuncCall (idName i) a_inArg a_out
    in
    Call Pre $ CAFuncCall { conc_fcall = FuncCall (idName i) c_inArg c_out
                          , abs_fcall = acall }

abstractedMod :: Abstracted ConcAbsFuncCall -> Maybe T.Text
abstractedMod = nameModule . caFuncName . abstract

hasPreArgError :: CounterExample ConcAbsFuncCall -> Bool
hasPreArgError (DirectCounter _ _) = False
hasPreArgError (CallsCounter _ calls_f _) = hasArgError . conc_fcall $ real calls_f

hasAbstractedArgError :: CounterExample ConcAbsFuncCall -> Bool
hasAbstractedArgError (DirectCounter _ as) = any (hasArgError . conc_fcall . real) as
hasAbstractedArgError (CallsCounter _ _ as) = any (hasArgError . conc_fcall . real) as

hasArgError :: FuncCall -> Bool
hasArgError = any isError . arguments

isError :: Expr -> Bool
isError (Prim Error _) = True
isError (Prim Undefined _) = True
isError _ = False