{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module G2.Liquid.Inference.G2Calls ( MeasureExs
                                   , MaxMeasures
                                   , PreEvals
                                   , PostEvals
                                   , FCEvals
                                   , Evals (..)

                                   , SpreadOutSolver (..)

                                   , gatherAllowedCalls

                                   , runLHInferenceAll

                                   , runLHInferenceCore
                                   , runLHCExSearch
                                   , checkFuncCall
                                   , checkCounterexample
                                   
                                   , emptyEvals
                                   , preEvals
                                   , postEvals
                                   , checkPre
                                   , checkPost
                                   , lookupEvals
                                   , mapEvals
                                   , mapAccumLEvals
                                   , deleteEvalsForFunc
                                   , printEvals

                                   , evalMeasures
                                   , formMeasureComps
                                   , chainReturnType) where

import G2.Config

import G2.Execution
import G2.Interface
import G2.Language as G2
import qualified G2.Language.ExprEnv as E
import qualified G2.Language.PathConds as PC
import G2.Lib.Printers
import G2.Liquid.Inference.Config
import G2.Liquid.AddCFBranch
import G2.Liquid.Conversion
import G2.Liquid.G2Calls
import G2.Liquid.Helpers
import G2.Liquid.Interface
import G2.Liquid.LHReducers
import G2.Liquid.TCValues
import G2.Liquid.Types
import G2.Liquid.TyVarBags
import G2.Liquid.Inference.InfStack
import G2.Liquid.Inference.Initalization
import G2.Solver hiding (Assert)
import G2.Translation

import Language.Haskell.Liquid.Types hiding (Config, hs)

import qualified Data.HashSet as HS
import qualified Data.HashMap.Lazy as HM
import Data.List
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Text as T

import Control.Monad
import Control.Exception
import Control.Monad.IO.Class
import Data.Monoid

-------------------------------------
-- Solvers
-------------------------------------

-- | A solver that adds soft asserts to (try to) spread out integer values
-- returned in a model.
data SpreadOutSolver solver = SpreadOutSolver Integer solver

instance Solver solver => Solver (SpreadOutSolver solver) where
    check (SpreadOutSolver _ solver) s pc = check solver s pc
    
    solve (SpreadOutSolver mx_size solver) s b is pc =
        let
            int_vs = filter (isInteger . typeOf) is
            max_vs = map (\i -> Id (Name "MAX_INT_ORD__??__" Nothing i Nothing) TyLitInt)
                   . map fst
                   $ zip [1..] int_vs

            max_vs_eq = map (flip ExtCond True)
                      $ map (\mv -> foldr1 or_expr $ map (\iv -> abs_expr (Var iv) `eq` Var mv) int_vs) max_vs
            max_ord = map (flip ExtCond True) . map (\(x, y) -> Var x `le_expr` Var y) $ adj max_vs
            soft_space = map SoftPC
                       . map (flip ExtCond True)
                       . map (\(v, vs) -> sum_vars vs `lt_expr` Var v)
                       . map (\(v:vs) -> (v, vs))
                       . filter (not . null)
                       . inits $ reverse max_vs

            pc' = PC.fromList $ max_vs_eq ++ max_ord ++ soft_space
            pc_union = pc `PC.union` pc'
        in
        case null int_vs of
            False -> do
                solve solver s b is pc_union
            True -> solve solver s b is pc
        where
            isInteger TyLitInt = True
            isInteger _ = False

            abs_expr x = App (Prim Abs TyUnknown) x
            eq x y = App (App (Prim Eq TyUnknown) x) y
            or_expr x y = App (App (Prim Or TyUnknown) x) y
            le_expr x y = App (App (Prim Le TyUnknown) x) y
            lt_expr x y = App (App (Prim Lt TyUnknown) x) y
            plus_expr x y = App (App (Prim Plus TyUnknown) x) y
            mult_expr x y = App (App (Prim Mult TyUnknown) x) y

            sum_vars = foldr plus_expr (Lit (LitInt mx_size))
                     . map (mult_expr (Lit (LitInt mx_size)))
                     . map Var

            adj xs = zip xs $ tail xs

    close (SpreadOutSolver _ solver) = close solver

-------------------------------------
-- Generating Allowed Inputs/Outputs
-------------------------------------

-- By symbolically executing from user-specified functions, and gathering
-- all called functions, we can get functions calls that MUST be allowed by
-- the specifications

gatherAllowedCalls :: T.Text
                   -> Maybe T.Text
                   -> LiquidReadyState
                   -> [GhcInfo]
                   -> InferenceConfig
                   -> Config
                   -> IO [FuncCall]
gatherAllowedCalls entry m lrs ghci infconfig config = do
    let config' = config -- { only_top = False }

    LiquidData { ls_state = s
               , ls_bindings = bindings
               , ls_memconfig = pres_names } <-
                    processLiquidReadyStateWithCall lrs ghci entry m config' mempty

    let (s', bindings') = (s, bindings) -- execStateM addTrueAssertsAll s bindings

    SomeSolver solver <- initSolver config'
    let simplifier = IdSimplifier
        s'' = repCFBranch $
               s' { true_assert = True
                  , track = [] :: [FuncCall] }

    (red, hal, ord) <- gatherReducerHalterOrderer infconfig config' solver simplifier
    (exec_res, bindings'') <- runG2WithSomes red hal ord solver simplifier pres_names s'' bindings'

    putStrLn $ "length exec_res = " ++ show (length exec_res)

    let called = concatMap (\er ->
                              let fs = final_state er in
                              map (fs,) $ track fs) exec_res

        fc_red = SomeReducer (StdRed (sharing config') solver simplifier)

    (_, red_calls) <- mapAccumM 
                                (\b (fs, fc) -> do
                                    (_, b', rfc) <- reduceFuncCall
                                                                       fc_red
                                                                       solver
                                                                       simplifier
                                                                       fs b fc
                                    return (b', rfc))
                                bindings''
                                called

    close solver

    return red_calls

repCFBranch :: ASTContainer t Expr => t -> t
repCFBranch = modifyASTs repCFBranch'

repCFBranch' :: Expr -> Expr
repCFBranch' nd@(NonDet (e:_))
    | Let b (Assert fc ae1 ae2) <- e = Let b $ Assume fc ae1 ae2
    | otherwise = nd
repCFBranch' (Let b (Assert fc ae1 ae2)) = Let b $ Assume fc ae1 ae2
repCFBranch' e = e

gatherReducerHalterOrderer :: (Solver solver, Simplifier simplifier)
                           => InferenceConfig
                           -> Config
                           -> solver
                           -> simplifier
                           -> IO (SomeReducer [FuncCall], SomeHalter [FuncCall], SomeOrderer [FuncCall])
gatherReducerHalterOrderer infconfig config solver simplifier = do
    let
        ng = mkNameGen ()

        share = sharing config

        state_name = Name "state" Nothing 0 Nothing

        m_logger = getLogger config

    timer_halter <- timerHalter (timeout_se infconfig * 3)

    return
        (SomeReducer (NonRedPCRed :<~| TaggerRed state_name ng)
            <~| (case m_logger of
                  Just logger -> SomeReducer (StdRed share solver simplifier :<~ Gatherer) <~ logger
                  Nothing -> SomeReducer (StdRed share solver simplifier :<~ Gatherer))
        , SomeHalter
            (DiscardIfAcceptedTag state_name
              -- :<~> searched_below
              :<~> SwitchEveryNHalter (switch_after config)
              :<~> SWHNFHalter
              :<~> timer_halter)
        , SomeOrderer (ToOrderer $ IncrAfterN 2000 (ADTSizeOrderer 0 Nothing)))

-------------------------------
-- Direct Counterexamples Calls
-------------------------------
-- This does all the work to take LH source code and run symbolic execution on the named function.
-- In the inference algorithm itself, we don't want to use this, since if we did we would be
-- needlessly repeatedly reading and compiling the code.  But it's to have an "end-to-end"
-- function to just running the symbolic execution, for debugging.

runLHInferenceAll :: MonadIO m
                  => InferenceConfig
                  -> Config
                  -> T.Text
                  -> [FilePath]
                  -> [FilePath]
                  -> [FilePath]
                  -> m (([ExecRes AbstractedInfo], Bindings), Id)
runLHInferenceAll infconfig config func proj fp lhlibs = do
    -- Initialize LiquidHaskell
    (ghci, lhconfig) <- liftIO $ getGHCI infconfig proj fp lhlibs

    let g2config = config { mode = Liquid
                          , steps = 2000 }
        transConfig = simplTranslationConfig { simpl = False }
    (main_mod, exg2) <- liftIO $ translateLoaded proj fp lhlibs transConfig g2config

    let (lrs, g2config', infconfig') = initStateAndConfig exg2 main_mod g2config infconfig ghci

    let configs = Configs { g2_config = g2config', lh_config = lhconfig, inf_config = infconfig'}

    execInfStack configs newProgress (runLHInferenceCore func main_mod lrs ghci)

-------------------------------
-- Generating Counterexamples
-------------------------------
runLHInferenceCore :: MonadIO m
                   => T.Text
                   -> Maybe T.Text
                   -> LiquidReadyState
                   -> [GhcInfo]
                   -> InfStack m (([ExecRes AbstractedInfo], Bindings), Id)
runLHInferenceCore entry m lrs ghci = do
    MaxSize max_coeff_sz <- maxSynthCoeffSizeI

    g2config <- g2ConfigM
    infconfig <- infConfigM

    LiquidData { ls_state = final_st
               , ls_bindings = bindings
               , ls_id = ifi
               , ls_counterfactual_name = cfn
               , ls_memconfig = pres_names } <- liftIO $ processLiquidReadyStateWithCall lrs ghci entry m g2config mempty
    SomeSolver solver <- liftIO $ initSolver g2config
    -- let solver' = SpreadOutSolver max_coeff_sz solver
    let simplifier = IdSimplifier
        final_st' = swapHigherOrdForSymGen bindings final_st

    (red, hal, ord) <- inferenceReducerHalterOrderer infconfig g2config solver simplifier entry m cfn final_st'
    (exec_res, final_bindings) <- liftIO $ runLHG2 g2config red hal ord solver simplifier pres_names ifi final_st' bindings

    liftIO $ close solver

    liftIO $ putStrLn "end runLHInferenceCore"

    return ((exec_res, final_bindings), ifi)

inferenceReducerHalterOrderer :: (MonadIO m, Solver solver, Simplifier simplifier)
                              => InferenceConfig
                              -> Config
                              -> solver
                              -> simplifier
                              -> T.Text
                              -> Maybe T.Text
                              -> Name
                              -> State LHTracker
                              -> InfStack m (SomeReducer LHTracker, SomeHalter LHTracker, SomeOrderer LHTracker)
inferenceReducerHalterOrderer infconfig config solver simplifier entry mb_modname cfn st = do
    extra_ce <- extraMaxCExI (entry, mb_modname)
    extra_time <- extraMaxTimeI (entry, mb_modname)

    let
        ng = mkNameGen ()

        share = sharing config

        state_name = Name "state" Nothing 0 Nothing
        abs_ret_name = Name "abs_ret" Nothing 0 Nothing

        -- searched_below = SearchedBelowHalter { found_at_least = 3
        --                                      , discarded_at_least = 6
        --                                      , discarded_at_most = 15 }
        ce_num = max_ce infconfig + extra_ce
        lh_max_outputs = LHMaxOutputsHalter ce_num

        timeout = timeout_se infconfig + extra_time

        m_logger = getLogger config

    liftIO $ putStrLn $ "ce num for " ++ T.unpack entry ++ " is " ++ show ce_num
    liftIO $ putStrLn $ "timeout for " ++ T.unpack entry ++ " is " ++ show timeout
    
    timer_halter <- liftIO $ timerHalter (timeout * 2)
    lh_timer_halter <- liftIO $ lhTimerHalter timeout

    let halter =      LHAbsHalter entry mb_modname (expr_env st)
                 :<~> lh_max_outputs
                 :<~> SwitchEveryNHalter (switch_after config)
                 -- :<~> LHLimitSameAbstractedHalter 5
                 :<~> LHSWHNFHalter
                 -- :<~> LHAcceptIfViolatedHalter
                 :<~> timer_halter
                 :<~> lh_timer_halter
                 -- :<~> OnlyIf (\pr _ -> any true_assert (accepted pr)) timer_halter

    return $
        (SomeReducer (NonRedAbstractReturns :<~| TaggerRed abs_ret_name ng)
            <~| (SomeReducer (NonRedPCRed :<~| TaggerRed state_name ng))
            <~| (case m_logger of
                  Just logger -> SomeReducer (StdRed share solver simplifier :<~ AllCallsRed :<~| RedArbErrors :<~| LHRed cfn :<~? ExistentialInstRed) <~ logger
                  Nothing -> SomeReducer (StdRed share solver simplifier :<~ AllCallsRed :<~| RedArbErrors :<~| LHRed cfn :<~? ExistentialInstRed))
        , SomeHalter
            (DiscardIfAcceptedTag state_name :<~> halter)
        , SomeOrderer (ToOrderer $ IncrAfterN 2000 (QuotTrueAssert (OrdComb (+) (PCSizeOrderer 0) (ADTSizeOrderer 0 (Just instFuncTickName))))))

runLHCExSearch :: MonadIO m
               => T.Text
               -> Maybe T.Text
               -> LiquidReadyState
               -> [GhcInfo]
               -> InfStack m (([ExecRes AbstractedInfo], Bindings), Id)
runLHCExSearch entry m lrs ghci = do
    g2config <- g2ConfigM
    infconfig <- infConfigM

    let g2config' = g2config { counterfactual = NotCounterfactual
                             , only_top = False}

    LiquidData { ls_state = final_st
               , ls_bindings = bindings
               , ls_id = ifi
               , ls_counterfactual_name = cfn
               , ls_memconfig = pres_names } <- liftIO $ processLiquidReadyStateWithCall lrs ghci entry m g2config' mempty
    SomeSolver solver <- liftIO $ initSolver g2config'
    let simplifier = IdSimplifier
        final_st' = swapHigherOrdForSymGen bindings final_st

    (red, hal, ord) <- realCExReducerHalterOrderer infconfig g2config' entry m solver simplifier cfn
    (exec_res, final_bindings) <- liftIO $ runLHG2 g2config' red hal ord solver simplifier pres_names ifi final_st' bindings

    liftIO $ close solver

    return ((exec_res, final_bindings), ifi)

realCExReducerHalterOrderer :: (MonadIO m, Solver solver, Simplifier simplifier)
                            => InferenceConfig
                            -> Config
                            -> T.Text
                            -> Maybe T.Text
                            -> solver
                            -> simplifier
                            -> Name
                            -> InfStack m (SomeReducer LHTracker, SomeHalter LHTracker, SomeOrderer LHTracker)
realCExReducerHalterOrderer infconfig config entry modname solver simplifier  cfn = do
    extra_ce <- extraMaxCExI (entry, modname)
    extra_depth <- extraMaxDepthI

    liftIO . putStrLn $ "extra_depth = " ++ show extra_depth

    let
        ng = mkNameGen ()

        share = sharing config

        state_name = Name "state" Nothing 0 Nothing
        abs_ret_name = Name "abs_ret" Nothing 0 Nothing

        -- searched_below = SearchedBelowHalter { found_at_least = 3
        --                                      , discarded_at_least = 6
        --                                      , discarded_at_most = 15 }
        ce_num = max_ce infconfig + extra_ce
        lh_max_outputs = LHMaxOutputsHalter ce_num

        m_logger = getLogger config

    timer_halter <- liftIO $ timerHalter (timeout_se infconfig)

    let halter =      lh_max_outputs
                 :<~> SwitchEveryNHalter (switch_after config)
                 :<~> ZeroHalter (0 + extra_depth)
                 :<~> LHAcceptIfViolatedHalter
                 :<~> timer_halter
                 -- :<~> OnlyIf (\pr _ -> any true_assert (accepted pr)) timer_halter

    return $
        (SomeReducer (NonRedAbstractReturns :<~| TaggerRed abs_ret_name ng)
            <~| (SomeReducer (NonRedPCRed :<~| TaggerRed state_name ng))
            <~| (case m_logger of
                  Just logger -> SomeReducer (StdRed share solver simplifier :<~| LHRed cfn) <~ logger
                  Nothing -> SomeReducer (StdRed share solver simplifier :<~| LHRed cfn))
        , SomeHalter
            (DiscardIfAcceptedTag state_name :<~> halter)
        , SomeOrderer (ToOrderer $ IncrAfterN 1000 (ADTSizeOrderer 0 Nothing)))


swapHigherOrdForSymGen :: Bindings -> State t -> State t
swapHigherOrdForSymGen b s@(State { curr_expr = CurrExpr er e }) =
    let
        is = filter (isTyFun . typeOf) $ inputIds s b

        e' = modify (swapForSG is) e
    in
    s { curr_expr = CurrExpr er e' }

swapForSG :: [Id] -> Expr -> Expr
swapForSG is e@(Var i)
    | i `elem` is =
        let
            as = map (\at -> case at of
                              NamedType i' -> (TypeL, i')
                              AnonType t -> (TermL, Id (Name "x" Nothing 0 Nothing) t))
               $ spArgumentTypes i
            r = returnType i

            sg_i = Id (Name "sym_gen" Nothing 0 Nothing) r
        in
        Let [(sg_i, SymGen r)] $ mkLams as (Var sg_i)
    | otherwise = e
swapForSG _ e = e

-------------------------------
-- Checking Counterexamples
-------------------------------

-- Does a given FuncCall (counterexample) violate a specification?
-- This allows us to check if a found counterexample violates a user-provided specifications,
-- or a synthesized specification.
-- Returns True if the original Assertions are True (i.e. not violated)
checkFuncCall :: LiquidReadyState -> [GhcInfo] -> Config -> FuncCall -> IO Bool
checkFuncCall = checkCounterexample

checkCounterexample :: LiquidReadyState -> [GhcInfo] -> Config -> FuncCall -> IO Bool
checkCounterexample lrs ghci config cex@(FuncCall { funcName = Name n m _ _ }) = do
    let config' = config { counterfactual = NotCounterfactual }
    -- We use the same function to instantiate this state as in runLHInferenceCore, so all the names line up
    LiquidData { ls_state = s
               , ls_bindings = bindings } <- processLiquidReadyStateWithCall lrs ghci n m config' mempty

    let s' = checkCounterexample' cex s

    SomeSolver solver <- initSolver config
    (fsl, _) <- genericG2Call config' solver s' bindings
    close solver

    -- We may return multiple states if any of the specifications contained a SymGen
    return $ any (currExprIsTrue . final_state) fsl

checkCounterexample' :: FuncCall -> State t -> State t
checkCounterexample' fc@(FuncCall { funcName = n }) s@(State { expr_env = eenv, known_values = kv })
    | Just e <- E.lookup n eenv =
    let
        e' = toJustSpec kv fc (leadingLamIds e) (inLams e)
    in
    s { curr_expr = CurrExpr Evaluate e'
      , true_assert = True }
    | otherwise = error $ "checkCounterexample': Name not found " ++ show n ++ "\n similar in eenv = "
                                      ++ show (E.keys $ E.filterWithKey (\(Name on _ _ _) _ -> on == nameOcc n ) eenv)

toJustSpec :: KnownValues -> FuncCall -> [Id] -> Expr -> Expr
toJustSpec _ (FuncCall { arguments = ars, returns = ret }) is (Let [(b, _)] (Assert _ e _)) =
    let
        rep = (Var b, ret):zip (map Var is) ars  
    in
    foldr (uncurry replaceASTs) e rep
toJustSpec kv _ _ e = assert (not $ hasAssert e) mkTrue kv

hasAssert :: Expr -> Bool
hasAssert = getAny . evalASTs hasAssert'

hasAssert' :: Expr -> Any
hasAssert' (Assert _ _ _) = Any True
hasAssert' _ = Any False


currExprIsTrue :: State t -> Bool
currExprIsTrue (State { curr_expr = CurrExpr _ (Data (DataCon (Name dcn _ _ _) _))}) = dcn == "True"
currExprIsTrue _ = False

-------------------------------
-- Checking Pre and Post Conditions
-------------------------------
type PreEvals b = FCEvals b
type PostEvals b = FCEvals b
type FCEvals b = HM.HashMap Name (HM.HashMap FuncCall b)

data Evals b = Evals { pre_evals :: PreEvals b
                     , post_evals :: PostEvals b }
                     deriving Show

emptyEvals :: Evals b
emptyEvals = Evals { pre_evals = HM.empty, post_evals = HM.empty }

preEvals :: (InfConfigM m, MonadIO m) => Evals Bool -> LiquidReadyState -> [GhcInfo] -> [FuncCall] -> m (Evals Bool)
preEvals evals@(Evals { pre_evals = pre }) lrs ghci fcs = do
    (pre', _) <- foldM (uncurry (runEvals checkPre' ghci lrs)) (pre, HM.empty) fcs
    return $ evals { pre_evals = pre' }
    -- return . HM.fromList =<< mapM (\fc -> return . (fc,) =<< checkPre lrs ghci fc) fcs

postEvals :: (InfConfigM m, MonadIO m) => Evals Bool -> LiquidReadyState -> [GhcInfo] -> [FuncCall] -> m (Evals Bool)
postEvals evals@(Evals { post_evals = post }) lrs ghci fcs = do
    (post', _) <- foldM (uncurry (runEvals checkPost' ghci lrs)) (post, HM.empty) fcs
    return $ evals { post_evals = post' }

runEvals :: (InfConfigM m, MonadIO m) =>
            (LiquidData -> FuncCall -> m Bool)
         -> [GhcInfo]
         -> LiquidReadyState
         -> FCEvals Bool
         -> HM.HashMap (T.Text, Maybe T.Text) LiquidData
         -> FuncCall
         -> m (FCEvals Bool, HM.HashMap (T.Text, Maybe T.Text) LiquidData)
runEvals f ghci lrs hm ld_m fc =
    let
      n = zeroOutName $ funcName fc
      n_hm = maybe HM.empty id (HM.lookup n hm)
    in
    if fc `HM.member` n_hm
      then return (hm, ld_m)
      else do
        let nt = nameTuple (funcName fc)
        (ld, ld_m') <- case HM.lookup nt ld_m of
                            Just ld' -> return (ld', ld_m)
                            Nothing -> do
                                ld' <- checkPreOrPostLD ghci lrs fc
                                return (ld', HM.insert nt ld' ld_m)
        pr <- f ld fc
        return $ (HM.insert n (HM.insert fc pr n_hm) hm, ld_m')

checkPre :: (InfConfigM m, MonadIO m) => [GhcInfo] -> LiquidReadyState -> FuncCall -> m Bool
checkPre ghci lrs fc = do
    ld <- checkPreOrPostLD ghci lrs fc
    checkPre' ld fc

checkPre' :: (InfConfigM m, MonadIO m) => LiquidData -> FuncCall -> m Bool
checkPre' = checkPreOrPost' (zeroOutKeys . ls_assumptions) arguments

checkPost :: (InfConfigM m, MonadIO m) => [GhcInfo] -> LiquidReadyState -> FuncCall -> m Bool
checkPost ghci lrs fc = do
    ld <- checkPreOrPostLD ghci lrs fc
    checkPost' ld fc

checkPost' :: (InfConfigM m, MonadIO m) => LiquidData -> FuncCall -> m Bool
checkPost' = checkPreOrPost' (zeroOutKeys . ls_posts) (\fc -> arguments fc ++ [returns fc])

zeroOutKeys :: M.Map Name v -> M.Map Name v
zeroOutKeys = M.mapKeys zeroOutName

zeroOutName :: Name -> Name
zeroOutName (Name n m _ l) = Name n m 0 l

checkPreOrPostLD :: (InfConfigM m, MonadIO m)
                 => [GhcInfo] -> LiquidReadyState -> FuncCall -> m LiquidData
checkPreOrPostLD lrs ghci (FuncCall { funcName = Name n m _ _ }) = do
    config <- g2ConfigM
    let config' = config { counterfactual = NotCounterfactual }
    -- We use the same function to instantiate this state as in runLHInferenceCore, so all the names line up
    liftIO $ processLiquidReadyStateWithCall ghci lrs n m config' mempty

checkPreOrPost' :: (InfConfigM m, MonadIO m)
               => (LiquidData -> M.Map Name Expr) -> (FuncCall -> [Expr]) -> LiquidData -> FuncCall -> m Bool
checkPreOrPost' extract ars ld@(LiquidData { ls_state = s, ls_bindings = bindings }) cex = do
    config <- g2ConfigM

    -- We use the same function to instantiate this state as in runLHInferenceCore, so all the names line up
    case checkFromMap ars (extract ld) cex s of
        Just s' -> do
            SomeSolver solver <- liftIO $ initSolver config
            (fsl, _) <- liftIO $ genericG2Call config solver s' bindings
            liftIO $ close solver

            -- We may return multiple states if any of the specifications contained a SymGen
            return $ any (currExprIsTrue . final_state) fsl
        -- If there is no explicit specification, the specification is implicitly True
        Nothing -> return True

checkFromMap :: (FuncCall -> [Expr]) -> M.Map Name Expr -> FuncCall -> State t -> Maybe (State t)
checkFromMap ars specs fc@(FuncCall { funcName = n }) s =
    let
        e = M.lookup (zeroOutName n) specs
    in
    case e of
        Just e' ->
            let
                e'' = mkApp $ e':ars fc
            in
            Just $ s { curr_expr = CurrExpr Evaluate e''
                     , true_assert = True }
        Nothing -> Nothing

lookupEvals :: FuncCall -> FCEvals a -> Maybe a
lookupEvals fc@(FuncCall { funcName = n }) fce =
    HM.lookup fc =<< HM.lookup (zeroOutName n) fce

mapEvals :: (a -> b) -> Evals a -> Evals b
mapEvals f (Evals { pre_evals = pre, post_evals = post }) =
    Evals { pre_evals = HM.map (HM.map f) pre, post_evals = HM.map (HM.map f) post }

mapAccumLEvals :: (a -> b -> (a, c)) -> a -> Evals b -> (a, Evals c)
mapAccumLEvals f inital ev =
    let
        (inital', pre') = mapAccumL (mapAccumL f) inital (pre_evals ev) 
        (inital'', post') = mapAccumL (mapAccumL f) inital' (post_evals ev) 
    in
    (inital'', ev { pre_evals = pre', post_evals = post' })

deleteEvalsForFunc :: Name -> Evals a -> Evals a
deleteEvalsForFunc n (Evals { pre_evals = pre_ev, post_evals = post_ev }) =
    Evals { pre_evals = HM.delete (zeroOutName n) pre_ev
          , post_evals = HM.delete (zeroOutName n) post_ev }

printEvals :: (a -> String) -> Evals a -> String
printEvals f (Evals { pre_evals = pre, post_evals = post }) =
    "Evals {\npre_evals = " ++ printEvals' f pre ++ "\npost_evals = " ++ printEvals' f post ++ "\n}"

printEvals' :: (a -> String) -> FCEvals a -> String
printEvals' f =
      intercalate "\n"
    . map (\(fc, v) -> printFuncCall fc ++ " -> " ++ f v)
    . HM.toList
    . HM.unions
    . HM.elems

-------------------------------
-- Eval Measures
-------------------------------
-- Evaluate all relevant measures on a given expression

type MeasureExs = HM.HashMap Expr (HM.HashMap [Name] Expr)

type MaxMeasures = Int

evalMeasures :: (InfConfigM m, ProgresserM m, MonadIO m) => MeasureExs -> LiquidReadyState -> [GhcInfo] -> [Expr] -> m MeasureExs
evalMeasures init_meas lrs ghci es = do
    config <- g2ConfigM
    let config' = config { counterfactual = NotCounterfactual }

    let memc = emptyMemConfig { pres_func = presMeasureNames }
    LiquidData { ls_state = s
               , ls_bindings = bindings
               , ls_measures = meas
               , ls_tcv = tcv
               , ls_memconfig = pres_names } <- liftIO $ extractWithoutSpecs lrs (Id (Name "" Nothing 0 Nothing) TyUnknown) ghci memc

    let s' = s { true_assert = True }
        (final_s, final_b) = markAndSweepPreserving pres_names s' bindings

        tot_meas = E.filter (isTotal (type_env s)) meas

    SomeSolver solver <- liftIO $ initSolver config
    meas_res <- foldM (evalMeasures' (final_s {type_env = type_env s}) final_b solver config' tot_meas tcv) init_meas $ filter (not . isError) es
    liftIO $ close solver
    return meas_res
    where
        meas_names = measureNames ghci
        meas_nameOcc = map (\(Name n md _ _) -> (n, md)) $ map symbolName meas_names

        presMeasureNames s _ hs =
            let
                eenv = E.filterWithKey (\(Name n md _ _) _ -> (n, md) `elem` meas_nameOcc) (expr_env s)
                eenv_meas_names = E.keys eenv
            in
            foldr HS.insert hs eenv_meas_names
    
        isError (Prim Error _) = True
        isError _ = False

isTotal :: TypeEnv -> Expr -> Bool
isTotal tenv = getAll . evalASTs isTotal'
    where
        isTotal' (Case i _ as)
            | TyCon n _:_ <- unTyApp (typeOf i)
            , Just adt <- M.lookup n tenv =
                All (length (dataCon adt) == length (filter isDataAlt as))
        isTotal' (Case _ _ _) = All False
        isTotal' _ = All True

        isDataAlt (G2.Alt (DataAlt _ _) _) = True
        isDataAlt _ = False


evalMeasures' :: ( InfConfigM m
                 , MonadIO m
                 , ProgresserM m
                 , ASTContainer t Expr
                 , ASTContainer t Type
                 , Named t
                 , Solver solver
                 , Show t) => State t -> Bindings -> solver -> Config -> Measures -> TCValues -> MeasureExs -> Expr -> m MeasureExs
evalMeasures' s bindings solver config meas tcv init_meas e =  do
    MaxSize max_meas <- maxSynthFormSizeM
    let m_sts = evalMeasures'' (fromInteger max_meas) s bindings meas tcv e

    foldM (\meas_exs (ns, e_in, s_meas) -> do
        case HM.lookup ns =<< HM.lookup e_in meas_exs of
            Just _ -> return meas_exs
            Nothing -> do
                (er, _) <- liftIO $ genericG2Call config solver s_meas bindings
                case er of
                    [er'] -> 
                        let 
                            e_out = conc_out er'
                        in
                        return $ HM.insertWith HM.union e_in (HM.singleton ns e_out) meas_exs
                    [] -> return $ HM.insertWith HM.union e_in (HM.singleton ns (Prim Undefined TyBottom)) meas_exs
                    _ -> error "evalMeasures': Bad G2 Call") init_meas m_sts

evalMeasures'' :: Int -> State t -> Bindings -> Measures -> TCValues -> Expr -> [([Name], Expr, State t)]
evalMeasures'' mx_meas s b m tcv e =
    let
        meas_comps = formMeasureComps mx_meas (type_env s) (typeOf e) m

        rel_m = mapMaybe (\ns_me ->
                              case chainReturnType (typeOf e) (map snd ns_me) of
                                  Just (_, vms) -> Just (ns_me, vms)
                                  Nothing -> Nothing) meas_comps
    in
    map (\(ns_es, bound) ->
            let
                is = map (\(n, me) -> Id n (typeOf me)) ns_es
                str_call = evalMeasuresCE s b tcv is e bound
            in
            (map fst ns_es, e, s { curr_expr = CurrExpr Evaluate str_call })
        ) rel_m

-- Form all possible measure compositions, up to the maximal length
formMeasureComps :: MaxMeasures -- ^ max length
                 -> TypeEnv
                 -> Type -- ^ Type of input value to the measures
                 -> Measures
                 -> [[(Name, Expr)]]
formMeasureComps !mx tenv in_t meas =
    let
        meas' = E.toExprList $ E.filter (isTotal tenv) meas
    in
    formMeasureComps' mx in_t (map (:[]) meas') meas'

formMeasureComps' :: MaxMeasures -- ^ max length
                  -> Type -- ^ Type of input value to the measures
                  -> [[(Name, Expr)]]
                  -> [(Name, Expr)]
                  -> [[(Name, Expr)]]
formMeasureComps' !mx in_t existing ns_me
    | mx <= 1 = existing
    | otherwise =
      let 
          r = [ ne1:ne2 | ne1@(_, e1) <- ns_me
                        , ne2 <- existing
                        , case (filter notLH $ anonArgumentTypes e1, fmap fst . chainReturnType in_t $ map snd ne2) of
                            ([at], Just t) -> PresType t .:: at
                            _ -> False ]
      in
      formMeasureComps' (mx - 1) in_t (r ++ existing) ns_me

chainReturnType :: Type -> [Expr] -> Maybe (Type, [M.Map Name Type])
chainReturnType t ne =
    foldM (\(t', vms) et -> 
                case filter notLH . anonArgumentTypes $ PresType et of
                    [at]
                        | (True, vm) <- t' `specializes` at -> Just (applyTypeMap vm . returnType $ PresType et, vm:vms)
                    _ ->  Nothing) (t, []) (map typeOf $ reverse ne)

notLH :: Type -> Bool
notLH ty
    | TyCon (Name n _ _ _) _ <- tyAppCenter ty = n /= "lh"
    | otherwise = True

evalMeasuresCE :: State t -> Bindings -> TCValues -> [Id] -> Expr -> [M.Map Name Type] -> Expr
evalMeasuresCE s bindings tcv is e bound =
    let
        meas_call = map (uncurry tyAppId) $ zip is bound
        ds = deepseq_walkers bindings

        call =  foldr App e meas_call
        str_call = mkStrict_maybe ds call
        lh_dicts_call = maybe call (fillLHDictArgs ds)  str_call
    in
    lh_dicts_call
    where
        tyAppId i b =
            let
                bound_names = map idName $ tyForAllBindings i
                bound_tys = map (\n -> case M.lookup n b of
                                        Just t -> t
                                        Nothing -> TyUnknown) bound_names
                lh_dcts = map (\t -> case lookupTCDict (type_classes s) (lhTC tcv) t of
                                          Just tc -> Var tc
                                          Nothing -> Prim Undefined TyBottom) bound_tys -- map (const $ Prim Undefined TyBottom) bound_tys
            in
            mkApp $ Var i:map Type bound_tys ++ lh_dcts

-------------------------------
-- Generic
-------------------------------
genericG2Call :: ( ASTContainer t Expr
                 , ASTContainer t Type
                 , Named t
                 , Solver solver) => Config -> solver -> State t -> Bindings -> IO ([ExecRes t], Bindings)
genericG2Call config solver s bindings = do
    let simplifier = IdSimplifier
        share = sharing config

    fslb <- runG2WithSomes (SomeReducer (StdRed share solver simplifier))
                           (SomeHalter SWHNFHalter)
                           (SomeOrderer NextOrderer)
                           solver simplifier PreserveAllMC s bindings

    return fslb

genericG2CallLogging :: ( ASTContainer t Expr
                        , ASTContainer t Type
                        , Named t
                        , Show t
                        , Solver solver) => Config -> solver -> State t -> Bindings -> String -> IO ([ExecRes t], Bindings)
genericG2CallLogging config solver s bindings lg = do
    let simplifier = IdSimplifier
        share = sharing config

    fslb <- runG2WithSomes (SomeReducer (StdRed share solver simplifier :<~ Logger lg))
                           (SomeHalter SWHNFHalter)
                           (SomeOrderer NextOrderer)
                           solver simplifier PreserveAllMC s bindings

    return fslb
