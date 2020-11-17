{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module G2.Liquid.Inference.Interface ( inferenceCheck
                                     , inference) where

import G2.Config.Config as G2
import qualified G2.Initialization.Types as IT
import G2.Interface hiding (violated)
import G2.Language.CallGraph
import G2.Language.Expr
import qualified G2.Language.ExprEnv as E
import G2.Language.Naming
import G2.Language.Support
import G2.Language.Syntax
import G2.Language.Typing
import G2.Liquid.AddTyVars
import G2.Liquid.Inference.Config
import G2.Liquid.Inference.FuncConstraint as FC
import G2.Liquid.Inference.G2Calls
import G2.Liquid.Inference.PolyRef
import G2.Liquid.Inference.Sygus
import G2.Liquid.Inference.GeneratedSpecs
import G2.Liquid.Inference.Verify
import G2.Liquid.Interface
import G2.Liquid.Types
import G2.Solver
import G2.Translation

import Language.Haskell.Liquid.Types as LH

import Control.Monad
import Control.Monad.Extra
import Control.Monad.IO.Class 
import qualified Data.Map as M
import Data.Either
import qualified Data.HashSet as S
import qualified Data.HashMap.Lazy as HM
import Data.List
import Data.Maybe
import qualified Data.Text as T

import qualified Language.Fixpoint.Types.Config as FP

import Debug.Trace

-- Run inference, with an extra, final check of correctness at the end.
-- Assuming inference is working correctly, this check should neve fail.
inferenceCheck :: InferenceConfig -> G2.Config -> [FilePath] -> [FilePath] -> [FilePath] -> IO (Either [CounterExample] GeneratedSpecs)
inferenceCheck infconfig config proj fp lhlibs = do
    (ghci, lhconfig) <- getGHCI infconfig config proj fp lhlibs
    res <- inference' infconfig config lhconfig ghci proj fp lhlibs
    case res of
        Right gs -> do
            check_res <- checkGSCorrect infconfig lhconfig ghci gs
            case check_res of
                Safe -> return res
                _ -> error "inferenceCheck: Check failed"
        _ -> return res

inference :: InferenceConfig -> G2.Config -> [FilePath] -> [FilePath] -> [FilePath] -> IO (Either [CounterExample] GeneratedSpecs)
inference infconfig config proj fp lhlibs = do
    -- Initialize LiquidHaskell
    (ghci, lhconfig) <- getGHCI infconfig config proj fp lhlibs
    inference' infconfig config lhconfig ghci proj fp lhlibs

inference' :: InferenceConfig
           -> G2.Config
           -> LH.Config
           -> [GhcInfo]
           -> [FilePath]
           -> [FilePath]
           -> [FilePath]
           -> IO (Either [CounterExample] GeneratedSpecs)
inference' infconfig config lhconfig ghci proj fp lhlibs = do
    mapM (print . gsQualifiers . spec) ghci

    -- Initialize G2
    let g2config = config { mode = Liquid
                          , steps = 2000 }
        transConfig = simplTranslationConfig { simpl = False }
    (main_mod, exg2) <- translateLoaded proj fp lhlibs transConfig g2config

    let simp_s = initSimpleState exg2
        (g2config', infconfig') = adjustConfig main_mod simp_s g2config infconfig ghci

        lrs = createStateForInference simp_s g2config' ghci

        eenv = expr_env . state . lr_state $ lrs

        cg = getCallGraph $ eenv
        nls = filter (not . null)
             . map (filter (\(Name _ m _ _) -> m == main_mod))
             $ nameLevels cg 

    putStrLn $ "cg = " ++ show (filter (\(Name _ m _ _) -> m == main_mod) . functions $ getCallGraph eenv)
    putStrLn $ "nls = " ++ show nls

    let configs = Configs { g2_config = g2config', lh_config = lhconfig, inf_config = infconfig'}
        prog = newProgress

    SomeSMTSolver smt <- getSMT g2config'
    let infL = iterativeInference smt ghci main_mod lrs nls HM.empty initMaxSize emptyGS emptyFC

    runConfigs (runProgresser infL prog) configs

getGHCI :: InferenceConfig -> G2.Config -> [FilePath] -> [FilePath] -> [FilePath] -> IO ([GhcInfo], LH.Config)
getGHCI infconfig config proj fp lhlibs = do
    lhconfig <- defLHConfig proj lhlibs
    let lhconfig' = lhconfig { pruneUnsorted = True
                             -- Block qualifiers being auto-generated by LH
                             , maxParams = if keep_quals infconfig then maxParams lhconfig else 0
                             , eliminate = if keep_quals infconfig then eliminate lhconfig else FP.All
                             , higherorderqs = False
                             , scrapeImports = False
                             , scrapeInternals = False
                             , scrapeUsedImports = False }
    ghci <- ghcInfos Nothing lhconfig' fp
    return (ghci, lhconfig)

data InferenceRes = CEx [CounterExample]
                  | Env GeneratedSpecs MeasureExs Size SMTModel
                  | Raise MeasureExs FuncConstraints MaxSizeConstraints NewFC
                  deriving (Show)

-- When we try to synthesize a specification for a function that we have already found a specification for,
-- we have to return to when we originally synthesized that specification.  We pass the newly aquired
-- FuncConstraints as RisignFuncConstraints
type RisingFuncConstraints = FuncConstraints

type Level = Int
type NameLevels = [[Name]]

type MaxSizeConstraints = FuncConstraints

iterativeInference :: (ProgresserM m, InfConfigM m, MonadIO m, SMTConverter con ast out io)
                   => con
                   -> [GhcInfo]
                   -> Maybe T.Text
                   -> LiquidReadyState
                   -> NameLevels
                   -> MeasureExs
                   -> MaxSize
                   -> GeneratedSpecs
                   -> FuncConstraints
                   -> m (Either [CounterExample] GeneratedSpecs)
iterativeInference con ghci m_modname lrs nls meas_ex max_sz gs fc = do
    res <- inferenceL con ghci m_modname lrs nls emptyEvals meas_ex max_sz gs fc emptyFC HM.empty
    case res of
        CEx cex -> return $ Left cex
        Env gs _ _ _ -> return $ Right gs
        Raise r_meas_ex r_fc _ _ -> do
            incrMaxDepthM
            -- We might be missing some internal GHC types from our deep_seq walkers
            -- We filter them out to avoid an error
            let eenv = expr_env . state $ lr_state lrs
                check = filter (\n -> 
                                  case E.lookup n eenv of
                                      Just e -> isJust $ 
                                              mkStrict_maybe 
                                              (deepseq_walkers $ lr_binding lrs) 
                                              (Var (Id (Name "" Nothing 0 Nothing) (returnType e)))
                                      Nothing -> False) (head nls)
            liftIO . putStrLn $ "head nls =  " ++ show (head nls)
            liftIO . putStrLn $ "iterativeInference check =  " ++ show check
            ref <- getCEx ghci m_modname lrs gs check
            case ref of
                Left cex -> return $ Left cex
                Right fc' -> iterativeInference con ghci m_modname lrs nls r_meas_ex (incrMaxSize max_sz) gs (unionFC fc' r_fc)


inferenceL :: (ProgresserM m, InfConfigM m, MonadIO m, SMTConverter con ast out io)
           => con
           -> [GhcInfo]
           -> Maybe T.Text
           -> LiquidReadyState
           -> NameLevels
           -> Evals Bool
           -> MeasureExs
           -> MaxSize
           -> GeneratedSpecs
           -> FuncConstraints
           -> MaxSizeConstraints
           -> HM.HashMap Size [(ModelNames, SMTModel)]
           -> m InferenceRes
inferenceL con ghci m_modname lrs nls evals meas_ex max_sz senv fc max_fc mdls = do
    let (fs, sf, below_sf) = case nls of
                        (fs_:sf_:be) -> (fs_, sf_, be)
                        ([fs_])-> (fs_, [], [])
                        [] -> ([], [], [])

    (resAtL, evals') <- inferenceB con ghci m_modname lrs nls evals meas_ex max_sz senv fc max_fc mdls
    -- let curr_ghci = addSpecsToGhcInfos ghci gs
    -- evals' <- updateEvals curr_ghci lrs fc evals
    -- synth_gs <- synthesize con curr_ghci lrs evals' meas_ex max_sz (unionFC max_fc fc) mdls (concat below_sf) sf

    liftIO $ do
        putStrLn "-------"
        putStrLn $ "lengths = " ++ show (HM.map (length . nub) mdls)
        putStrLn "-------"

    case resAtL of
        Env senv' meas_ex' sz smt_mdl -> 
            case nls of
                [] -> return resAtL
                (_:nls') -> do
                    liftIO $ putStrLn "Down a level!"
                    let evals'' = foldr deleteEvalsForFunc evals' sf
                    inf_res <- inferenceL con ghci m_modname lrs nls' evals'' meas_ex' max_sz senv' fc max_fc HM.empty
                    case inf_res of
                        Raise r_meas_ex r_fc r_max_fc has_new -> do
                            liftIO $ putStrLn "Up a level!"
                            
                            mdls' <- adjModelAndMaxCEx has_new sz smt_mdl mdls
                            inferenceL con ghci m_modname lrs nls evals' r_meas_ex max_sz senv r_fc r_max_fc mdls'
                        _ -> return inf_res
        _ -> return resAtL

inferenceB :: (ProgresserM m, InfConfigM m, MonadIO m, SMTConverter con ast out io)
           => con
           -> [GhcInfo]
           -> Maybe T.Text
           -> LiquidReadyState
           -> NameLevels
           -> Evals Bool
           -> MeasureExs
           -> MaxSize
           -> GeneratedSpecs
           -> FuncConstraints
           -> MaxSizeConstraints
           -> HM.HashMap Size [(ModelNames, SMTModel)]
           -> m (InferenceRes, Evals Bool)
inferenceB con ghci m_modname lrs nls evals meas_ex max_sz gs fc max_fc mdls = do
    let (fs, sf, below_sf) = case nls of
                        (fs_:sf_:be) -> (fs_, sf_, be)
                        ([fs_])-> (fs_, [], [])
                        [] -> ([], [], [])

    let curr_ghci = addSpecsToGhcInfos ghci gs
    evals' <- updateEvals curr_ghci lrs fc evals
    synth_gs <- synthesize con curr_ghci lrs evals' meas_ex max_sz (unionFC max_fc fc) mdls (concat below_sf) sf

    liftIO $ do
        putStrLn "-------"
        putStrLn $ "lengths = " ++ show (HM.map (length . nub) mdls)
        putStrLn "-------"

    case synth_gs of
        SynthEnv envN sz smt_mdl -> do
            let gs' = unionDroppingGS gs envN
                ghci' = addSpecsToGhcInfos ghci gs'
            liftIO $ do
                putStrLn "inferenceB"
                putStrLn $ "fs = " ++ show fs
                putStrLn $ "init gs' = " ++ show gs'

            res <- tryToVerifyOnly ghci' fs

            liftIO . putStrLn $ "res = " ++ show res
            
            case res of
                Safe -> return $ (Env gs' meas_ex sz smt_mdl, evals')
                Unsafe bad -> do
                    ref <- refineUnsafe ghci m_modname lrs gs' bad
                    case ref of
                        Left cex -> return $ (CEx cex, evals')
                        Right fc' -> do
                            liftIO $ putStrLn "Before genMeasureExs"
                            meas_ex' <- updateMeasureExs meas_ex lrs ghci fc'
                            liftIO $ putStrLn "After genMeasureExs"

                            mdls' <- adjModelAndMaxCEx (hasNewFC fc' fc) sz smt_mdl mdls
                            inferenceB con ghci m_modname lrs nls evals' meas_ex' max_sz gs (unionFC fc fc') max_fc mdls'
                Crash _ _ -> error "inferenceB: LiquidHaskell crashed"
        SynthFail sf_fc -> return $ (Raise meas_ex fc (unionFC max_fc sf_fc) (hasNewFC sf_fc max_fc), evals')

refineUnsafe :: (ProgresserM m, InfConfigM m, MonadIO m) => [GhcInfo] -> Maybe T.Text -> LiquidReadyState
             -> GeneratedSpecs
             -> [Name] -> m (Either [CounterExample] FuncConstraints)
refineUnsafe ghci m_modname lrs gs bad = do
    let merged_se_ghci = addSpecsToGhcInfos ghci gs

    liftIO $ mapM_ (print . gsTySigs . spec) merged_se_ghci

    let bad' = nub $ map nameOcc bad

    res <- mapM (genNewConstraints merged_se_ghci m_modname lrs) bad'

    liftIO $ do
        putStrLn $ "res = "
        printCE $ concat res

    let res' = filter (not . hasAbstractedArgError) . concat $ res

    -- Either converts counterexamples to FuncConstraints, or returns them as errors to
    -- show to the user.
    new_fc <- checkNewConstraints ghci lrs res'

    case new_fc of
        Left cex -> return $ Left cex
        Right new_fc' -> do
            liftIO . putStrLn $ "new_fc' = " ++ printFCs new_fc'
            return $ Right new_fc'

adjModelAndMaxCEx :: ProgresserM m => NewFC -> Size -> SMTModel
                  -> HM.HashMap Size [(ModelNames, SMTModel)] -> m (HM.HashMap Size [(ModelNames, SMTModel)])
adjModelAndMaxCEx has_new sz smt_mdl mdls = do
      case has_new of
            NewFC -> return mdls
            NoNewFC repeated_fc
                | not $ nullFC repeated_fc -> do
                    let ns = map funcName $ allCallsFC repeated_fc
                        mdls' = HM.insertWith (++) sz [(MNOnly ns, smt_mdl)] mdls                                      
                    incrMaxCExM
                    return mdls'
                | otherwise -> do
                    let mdls' = HM.insertWith (++) sz [(MNAll, smt_mdl)] mdls
                    incrMaxCExM
                    return mdls'

genNewConstraints :: (ProgresserM m, InfConfigM m, MonadIO m) => [GhcInfo] -> Maybe T.Text -> LiquidReadyState -> T.Text -> m [CounterExample]
genNewConstraints ghci m lrs n = do
    liftIO . putStrLn $ "Generating constraints for " ++ T.unpack n
    ((exec_res, _), i) <- runLHInferenceCore n m lrs ghci
    let exec_res' = filter (true_assert . final_state) exec_res
    return $ map (lhStateToCE i) exec_res'

getCEx :: (ProgresserM m, InfConfigM m, MonadIO m) => [GhcInfo] -> Maybe T.Text -> LiquidReadyState
             -> GeneratedSpecs
             -> [Name] -> m (Either [CounterExample] FuncConstraints)
getCEx ghci m_modname lrs gs bad = do
    let merged_se_ghci = addSpecsToGhcInfos ghci gs

    liftIO $ mapM_ (print . gsTySigs . spec) merged_se_ghci

    let bad' = nub $ map nameOcc bad

    res <- mapM (checkForCEx merged_se_ghci m_modname lrs) bad'

    liftIO $ do
        putStrLn $ "getCEx res = "
        printCE $ concat res

    let res' = concat res

    -- Either converts counterexamples to FuncConstraints, or returns them as errors to
    -- show to the user.
    new_fc <- checkNewConstraints ghci lrs res'

    case new_fc of
        Left cex -> return $ Left cex
        Right new_fc' -> do
            liftIO . putStrLn $ "new_fc' = " ++ printFCs new_fc'
            return $ Right new_fc'

checkForCEx :: (ProgresserM m, InfConfigM m, MonadIO m) => [GhcInfo] -> Maybe T.Text -> LiquidReadyState -> T.Text -> m [CounterExample]
checkForCEx ghci m lrs n = do
    liftIO . putStrLn $ "Checking CEx for " ++ T.unpack n
    ((exec_res, _), i) <- runLHCExSearch n m lrs ghci
    let exec_res' = filter (true_assert . final_state) exec_res
    return $ map (lhStateToCE i) exec_res'

createStateForInference :: SimpleState -> G2.Config -> [GhcInfo] -> LiquidReadyState
createStateForInference simp_s config ghci =
    let
        (simp_s', ph_tyvars) = if add_tyvars config
                                then fmap Just $ addTyVarsEEnvTEnv simp_s
                                else (simp_s, Nothing)
        (s, b) = initStateFromSimpleState simp_s' True 
                    (\_ ng _ _ _ _ -> (Prim Undefined TyBottom, [], [], ng))
                    (E.higherOrderExprs . IT.expr_env)
                    config
    in
    createLiquidReadyState s b ghci ph_tyvars config


checkNewConstraints :: (InfConfigM m, MonadIO m) => [GhcInfo] -> LiquidReadyState -> [CounterExample] -> m (Either [CounterExample] FuncConstraints)
checkNewConstraints ghci lrs cexs = do
    g2config <- g2ConfigM
    infconfig <- infConfigM
    res <- mapM (cexsToBlockingFC lrs ghci) cexs
    res2 <- return . concat =<< mapM cexsToExtraFC cexs
    case lefts res of
        res'@(_:_) -> return . Left $ res'
        _ -> return . Right . unionsFC . map fromSingletonFC $ (rights res) ++ res2

updateMeasureExs :: (InfConfigM m, MonadIO m) => MeasureExs -> LiquidReadyState -> [GhcInfo] -> FuncConstraints -> m MeasureExs
updateMeasureExs meas_ex lrs ghci fcs =
    let
        es = concatMap (\fc ->
                    let
                        cons = allCalls fc
                        vls = concatMap (\c -> returns c:arguments c) cons 
                        ex_poly = concat . concatMap extractValues . concatMap extractExprPolyBound $ vls
                    in
                    vls ++ ex_poly
                ) (toListFC fcs)
    in
    evalMeasures meas_ex lrs ghci es

synthesize :: (InfConfigM m, MonadIO m, SMTConverter con ast out io)
           => con -> [GhcInfo] -> LiquidReadyState -> Evals Bool -> MeasureExs
           -> MaxSize -> FuncConstraints -> HM.HashMap Size [(ModelNames, SMTModel)] -> [Name] -> [Name] -> m SynthRes
synthesize con ghci lrs evals meas_ex max_sz fc mdls to_be for_funcs = do
    liftIO . putStrLn $ "all fc = " ++ printFCs fc
    liaSynth con ghci lrs evals meas_ex max_sz fc mdls to_be for_funcs

updateEvals :: (InfConfigM m, MonadIO m) => [GhcInfo] -> LiquidReadyState -> FuncConstraints -> Evals Bool -> m (Evals Bool)
updateEvals ghci lrs fc evals = do
    let cs = allCallsFC fc

    liftIO $ putStrLn "Before check func calls"
    evals' <- preEvals evals lrs ghci cs
    liftIO $ putStrLn "After pre"
    evals'' <- postEvals evals' lrs ghci cs
    liftIO $ putStrLn "After check func calls"

    return evals''


data NewFC = NewFC
           | NoNewFC FuncConstraints -- ^ The contained set of FuncConstraints is not new
           deriving Show

hasNewFC :: FuncConstraints -> FuncConstraints -> NewFC
hasNewFC fc1 fc2
    | not . nullFC $ differenceFC fc1 fc2 = NewFC
    | otherwise = NoNewFC fc1

-- | Converts counterexamples into constraints that block the current specification set
cexsToBlockingFC :: (InfConfigM m, MonadIO m) => LiquidReadyState -> [GhcInfo] -> CounterExample -> m (Either CounterExample FuncConstraint)
cexsToBlockingFC _ _ (DirectCounter dfc fcs@(_:_))
    | (_:_, no_err_fcs) <- partition (hasArgError . abstract) fcs = undefined
    | isError (returns dfc) = do
        infconfig <- infConfigM
        let fcs' = filter (\fc -> abstractedMod fc `S.member` modules infconfig) fcs

        let rhs = OrFC $ map (\(Abstracted { abstract = fc }) -> 
                        ImpliesFC (Call Pre fc) (NotFC (Call Post fc))) fcs'

        return . Right $ ImpliesFC (Call Pre dfc) rhs
    | otherwise = do
        infconfig <- infConfigM
        let fcs' = filter (\fc -> abstractedMod fc `S.member` modules infconfig) fcs

        let lhs = AndFC [Call Pre dfc, NotFC (Call Post dfc)]
            rhs = OrFC $ map (\(Abstracted { abstract = fc }) -> 
                        ImpliesFC (Call Pre fc) (NotFC (Call Post fc))) fcs'

        if not . null $ fcs'
            then return . Right $ ImpliesFC lhs rhs
            else error "cexsToBlockingFC: Unhandled"
cexsToBlockingFC _ _ (CallsCounter dfc cfc fcs@(_:_))
    | (_:_, no_err_fcs) <- partition (hasArgError . abstract) fcs = undefined
    | otherwise = do
        infconfig <- infConfigM
        let fcs' = filter (\fc -> abstractedMod fc `S.member` modules infconfig) fcs

        let lhs = AndFC [Call Pre dfc, NotFC (Call Pre (abstract cfc))]
            rhs = OrFC $ map (\(Abstracted { abstract = fc }) -> 
                                ImpliesFC (Call Pre fc) (NotFC (Call Post fc))) fcs'

        if not . null $ fcs' 
            then return . Right $ ImpliesFC lhs rhs
            else error "cexsToBlockingFC: Should be unreachable! Non-refinable function abstracted!"    
cexsToBlockingFC lrs ghci cex@(DirectCounter dfc [])
    | isError (returns dfc) = do
        if isExported lrs (funcName dfc)
            then return . Left $ cex
            else return . Right . NotFC $ Call Pre dfc
    | isExported lrs (funcName dfc) = do
        post_ref <- checkPost ghci lrs dfc
        case post_ref of
            True -> return $ Right (Call All dfc)
            False -> return . Left $ cex
    | otherwise = return $ Right (Call All dfc)
cexsToBlockingFC lrs ghci cex@(CallsCounter dfc cfc [])
    | any isError (arguments (abstract cfc)) = do
        if
            | isExported lrs (funcName dfc)
            , isExported lrs (funcName (real cfc)) -> do
                called_pr <- checkPre ghci lrs (real cfc) -- TODO: Shouldn't be changing this?
                case called_pr of
                    True -> return . Right $ NotFC (Call Pre dfc)
                    False -> return . Left $ cex
            | isExported lrs (funcName dfc) -> do
                called_pr <- checkPre ghci lrs (real cfc)
                case called_pr of
                    True -> return . Right $ NotFC (Call Pre dfc)
                    False -> return . Left $ cex
            | otherwise -> return . Right $ NotFC (Call Pre dfc)
    | otherwise = do
        if
            | isExported lrs (funcName dfc)
            , isExported lrs (funcName (real cfc)) -> do
                called_pr <- checkPre ghci lrs (real cfc) -- TODO: Shouldn't be changing this?
                case called_pr of
                    True -> return . Right $ ImpliesFC (Call Pre dfc) (Call Pre (abstract cfc))
                    False -> return . Left $ cex
            | isExported lrs (funcName dfc) -> do
                called_pr <- checkPre ghci lrs (real cfc)
                case called_pr of
                    True -> return . Right $ ImpliesFC (Call Pre dfc) (Call Pre (abstract cfc))
                    False -> return . Left $ cex
            | otherwise -> return . Right $ ImpliesFC (Call Pre dfc) (Call Pre (abstract cfc))

-- Function constraints that don't block the current specification set, but which must be true
-- (i.e. the actual input and output for abstracted functions)
cexsToExtraFC :: InfConfigM m => CounterExample -> m [FuncConstraint]
cexsToExtraFC (DirectCounter _ fcs@(_:_)) = do
    infconfig <- infConfigM
    let fcs' = filter (\fc -> abstractedMod fc `S.member` modules infconfig) fcs
    return $ mapMaybe realToMaybeFC fcs'
cexsToExtraFC (CallsCounter _ cfc fcs@(_:_)) = do
    infconfig <- infConfigM
    let fcs' = filter (\fc -> abstractedMod fc `S.member` modules infconfig) fcs

    let abs = mapMaybe realToMaybeFC fcs'
        clls = if not . isError . returns . real $ cfc
                  then [Call All $ real cfc]
                  else []

    return $ clls ++ abs
cexsToExtraFC (DirectCounter fc []) = return []
cexsToExtraFC (CallsCounter dfc cfc [])
    | isError (returns dfc) = return []
    | isError (returns (real cfc)) = return []
    | any isError (arguments (real cfc)) = return []
    | otherwise =
        let
            call_all_dfc = Call All dfc
            call_all_cfc = Call All (real cfc)
            imp_fc = ImpliesFC (Call Pre dfc) (Call Pre $ real cfc)
        in
        return $ [call_all_dfc, call_all_cfc, imp_fc]

realToMaybeFC :: Abstracted -> Maybe FuncConstraint
realToMaybeFC a@(Abstracted { real = fc }) 
    | hits_lib_err_in_real a = Nothing
    | otherwise = Just $ ImpliesFC (Call Pre fc) (Call Post fc)

isExported :: LiquidReadyState -> Name -> Bool
isExported lrs n = n `elem` exported_funcs (lr_binding lrs)

hasUserSpec :: InfConfigM m => Name -> m Bool
hasUserSpec (Name n m _ _) = do
    infconfig <- infConfigM
    return $ (n, m) `S.member` pre_refined infconfig

getDirectCaller :: CounterExample -> Maybe FuncCall
getDirectCaller (CallsCounter f _ []) = Just f
getDirectCaller _ = Nothing

getDirectCalled :: CounterExample -> Maybe FuncCall
getDirectCalled (CallsCounter _ f []) = Just (abstract f)
getDirectCalled _ = Nothing

notRetError :: FuncCall -> Bool
notRetError (FuncCall { returns = Prim Error _ }) = False
notRetError _ = True

insertsFC :: [FuncConstraint] -> FuncConstraints
insertsFC = foldr insertFC emptyFC

abstractedMod :: Abstracted -> Maybe T.Text
abstractedMod = nameModule . funcName . abstract

hasAbstractedArgError :: CounterExample -> Bool
hasAbstractedArgError (DirectCounter _ abs) = any (hasArgError . real) abs
hasAbstractedArgError (CallsCounter _ _ abs) = any (hasArgError . real) abs

hasArgError :: FuncCall -> Bool
hasArgError = any isError . arguments

isError :: Expr -> Bool
isError (Prim Error _) = True
isError (Prim Undefined _) = True
isError _ = False