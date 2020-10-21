{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module G2.Liquid.Inference.G2Calls ( MeasureExs
                                   , PreEvals
                                   , PostEvals
                                   , FuncCallEvals
                                   , gatherAllowedCalls
                                   , runLHInferenceCore
                                   , checkFuncCall
                                   , checkCounterexample
                                   , preEvals
                                   , postEvals
                                   , evalMeasures) where

import G2.Config

import G2.Execution
import qualified G2.Initialization.Types as IT
import G2.Interface
import G2.Language
import qualified G2.Language.ExprEnv as E
import G2.Language.Monad
import G2.Liquid.Inference.Config
import G2.Liquid.Conversion
import G2.Liquid.G2Calls
import G2.Liquid.Helpers
import G2.Liquid.Interface
import G2.Liquid.LHReducers
import G2.Liquid.SpecialAsserts
import G2.Liquid.TCValues
import G2.Liquid.Types
import G2.Solver hiding (Assert)
import G2.Translation

import Language.Fixpoint.Types.Names
import Language.Haskell.Liquid.Types hiding (Config)

import GHC.Generics (Generic)
import Data.Data (Data, Typeable)
import Data.Hashable
import qualified Data.HashSet as HS
import qualified Data.HashMap.Lazy as HM
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Text as T

import Control.Monad
import Control.Exception
import Control.Monad.IO.Class
import Data.Monoid
import G2.Language.KnownValues

import Debug.Trace

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
    let config' = config { only_top = False }

    LiquidData { ls_state = s
               , ls_bindings = bindings
               , ls_memconfig = pres_names } <-
                    processLiquidReadyStateWithCall lrs ghci entry m config' mempty

    let (s', bindings') = execStateM addTrueAssertsAll s bindings

    SomeSolver solver <- initSolver config'
    let simplifier = ADTSimplifier arbValue
        s'' = repCFBranch (known_values s') $
               s' { true_assert = True
                  , track = [] :: [FuncCall] }

    (red, hal, ord) <- gatherReducerHalterOrderer infconfig config' solver simplifier entry m s''
    (exec_res, bindings'') <- runG2WithSomes red hal ord solver simplifier pres_names s'' bindings'

    putStrLn $ "length exec_res = " ++ show (length exec_res)

    let called = concatMap (\er ->
                              let fs = final_state er in
                              map (fs,) $ track fs) exec_res

        fc_red = SomeReducer (StdRed (sharing config') solver simplifier)

    (bindings''', red_calls) <- mapAccumM 
                                (\b (fs, fc) -> reduceFuncCall (sharing config') 
                                                               fc_red
                                                               solver
                                                               simplifier
                                                               fs b fc)
                                bindings''
                                called

    close solver

    return red_calls

repCFBranch :: ASTContainer t Expr => KnownValues -> t -> t
repCFBranch kv = modifyASTs (repCFBranch' kv)

repCFBranch' :: KnownValues -> Expr -> Expr
repCFBranch' kv nd@(NonDet (e:_))
    | Let b (Assert fc ae1 ae2) <- e = Let b $ Assume fc ae1 ae2
    | otherwise = nd
repCFBranch' kv (Let b (Assert fc ae1 ae2)) = Let b $ Assume fc ae1 ae2
repCFBranch' _ e = e

gatherReducerHalterOrderer :: (Solver solver, Simplifier simplifier)
                           => InferenceConfig
                           -> Config
                           -> solver
                           -> simplifier
                           -> T.Text
                           -> Maybe T.Text
                           -> State [FuncCall]
                           -> IO (SomeReducer [FuncCall], SomeHalter [FuncCall], SomeOrderer [FuncCall])
gatherReducerHalterOrderer infconfig config solver simplifier entry mb_modname st = do
    let
        ng = mkNameGen ()

        share = sharing config

        state_name = Name "state" Nothing 0 Nothing
    
    timer_halter <- timerHalter (timeout_se infconfig)

    return
        (SomeReducer (NonRedPCRed :<~| TaggerRed state_name ng)
            <~| (case logStates config of
                  Just fp -> SomeReducer (StdRed share solver simplifier :<~ Gatherer :<~ Logger fp)
                  Nothing -> SomeReducer (StdRed share solver simplifier :<~ Gatherer))
        , SomeHalter
            (DiscardIfAcceptedTag state_name
              -- :<~> searched_below
              :<~> SwitchEveryNHalter (switch_after config)
              :<~> SWHNFHalter
              :<~> timer_halter)
        , SomeOrderer (ToOrderer $ IncrAfterN 1000 ADTHeightOrderer))

data GathererReducer = Gatherer

instance Reducer GathererReducer () [FuncCall] where
    initReducer _ _ = ()

    redRules gr _ s@(State { curr_expr = CurrExpr Evaluate (e@(Assume (Just fc) _ _))
                           , track = tr
                           }) b =
        let
          s' = s { curr_expr = CurrExpr Evaluate e
                 , track = fc:tr}
        in
        return (Finished, [(s', ())], b, gr) 
    redRules gr _ s b = return (Finished, [(s, ())], b, gr)

-------------------------------
-- Generating Counterexamples
-------------------------------
runLHInferenceCore :: (ProgresserM m, InfConfigM m, MonadIO m)
                   => T.Text
                   -> Maybe T.Text
                   -> LiquidReadyState
                   -> [GhcInfo]
                   -> m (([ExecRes AbstractedInfo], Bindings), Id)
runLHInferenceCore entry m lrs ghci = do
    g2config <- g2ConfigM
    infconfig <- infConfigM

    LiquidData { ls_state = final_st
               , ls_bindings = bindings
               , ls_id = ifi
               , ls_counterfactual_name = cfn
               , ls_counterfactual_funcs = cf_funcs
               , ls_memconfig = pres_names } <- liftIO $ processLiquidReadyStateWithCall lrs ghci entry m g2config mempty
    SomeSolver solver <- liftIO $ initSolver g2config
    let simplifier = ADTSimplifier arbValue
        final_st' = swapHigherOrdForSymGen bindings final_st

    (red, hal, ord) <- inferenceReducerHalterOrderer infconfig g2config solver simplifier entry m cfn cf_funcs final_st'
    (exec_res, final_bindings) <- liftIO $ runLHG2 g2config red hal ord solver simplifier pres_names final_st' bindings

    liftIO $ close solver

    return ((exec_res, final_bindings), ifi)

inferenceReducerHalterOrderer :: (ProgresserM m, MonadIO m, Solver solver, Simplifier simplifier)
                              => InferenceConfig
                              -> Config
                              -> solver
                              -> simplifier
                              -> T.Text
                              -> Maybe T.Text
                              -> Name
                              -> HS.HashSet Name
                              -> State LHTracker
                              -> m (SomeReducer LHTracker, SomeHalter LHTracker, SomeOrderer LHTracker)
inferenceReducerHalterOrderer infconfig config solver simplifier entry mb_modname cfn cf_funcs st = do
    extra_ce <- extraMaxCExM (entry, mb_modname)

    let
        ng = mkNameGen ()

        share = sharing config

        (limHalt, limOrd) = limitByAccepted (cut_off config)
        state_name = Name "state" Nothing 0 Nothing

        -- searched_below = SearchedBelowHalter { found_at_least = 3
        --                                      , discarded_at_least = 6
        --                                      , discarded_at_most = 15 }
        ce_num = max_ce infconfig + extra_ce
        lh_max_outputs = LHMaxOutputsHalter ce_num

    liftIO $ putStrLn $ "ce num for " ++ T.unpack entry ++ " is " ++ show ce_num
    
    timer_halter <- liftIO $ timerHalter (timeout_se infconfig)

    return $ if higherOrderSolver config == AllFuncs then 
        ( SomeReducer NonRedPCRed
            <~| (case logStates config of
                  Just fp -> SomeReducer (StdRed share solver simplifier :<~| LHRed cfn :<~ Logger fp)
                  Nothing -> SomeReducer (StdRed share solver simplifier :<~| LHRed cfn))
        , SomeHalter
                (LHAbsHalter entry mb_modname (expr_env st)
                  -- :<~> searched_below
                  :<~> lh_max_outputs
                  :<~> SwitchEveryNHalter (switch_after config)
                  :<~> LHLimitSameAbstractedHalter 3
                  :<~> AcceptIfViolatedHalter
                  :<~> timer_halter)
        , SomeOrderer (ToOrderer $ IncrAfterN 1000 ADTHeightOrderer))
    else
        (SomeReducer (NonRedPCRed :<~| TaggerRed state_name ng)
            <~| (case logStates config of
                  Just fp -> SomeReducer (StdRed share solver simplifier :<~| LHRed cfn :<~ Logger fp)
                  Nothing -> SomeReducer (StdRed share solver simplifier :<~| LHRed cfn))
        , SomeHalter
            (DiscardIfAcceptedTag state_name
              :<~> LHAbsHalter entry mb_modname (expr_env st)
              -- :<~> searched_below
              :<~> lh_max_outputs
              :<~> SwitchEveryNHalter (switch_after config)
              :<~> LHLimitSameAbstractedHalter 3
              :<~> AcceptIfViolatedHalter
              :<~> timer_halter)
        , SomeOrderer (ToOrderer $ IncrAfterN 1000 ADTHeightOrderer))

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

abstractedWeight :: Processed (State LHTracker) -> State LHTracker -> Int -> Int
abstractedWeight pr s v =
    let
        abs_calls = map funcName . abstract_calls $ track s

        acc_abs_calls = filter (not . null)
                      . map (filter (`elem` abs_calls))
                      . map (map funcName . abstract_calls . track)
                      $ accepted pr
    in
    v + length (acc_abs_calls) * 200

checkBadTy :: State t -> Bindings -> Bool
checkBadTy s _ = getAny . evalASTs (checkBadTy' (known_values s)) $ expr_env s

checkBadTy' :: KnownValues -> Expr -> Any
checkBadTy' kv (Data (DataCon n (TyForAll _ (TyFun _ (TyFun _ _))))) = Any $ n == dcEmpty kv
checkBadTy' _ _ = Any False

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
type PreEvals = FuncCallEvals
type PostEvals = FuncCallEvals
type FuncCallEvals = HM.HashMap FuncCall Bool

preEvals :: (InfConfigM m, MonadIO m) => LiquidReadyState -> [GhcInfo] -> [FuncCall] -> m PreEvals
preEvals lrs ghci fcs =
    foldM (\hm fc -> if fc `HM.member` hm
                          then return hm
                          else do
                            pr <- checkPre lrs ghci fc
                            return (HM.insert fc pr hm)) HM.empty fcs
    -- return . HM.fromList =<< mapM (\fc -> return . (fc,) =<< checkPre lrs ghci fc) fcs

postEvals :: (InfConfigM m, MonadIO m) => LiquidReadyState -> [GhcInfo] -> [FuncCall] -> m PostEvals
postEvals lrs ghci fcs =
    foldM (\hm fc -> if fc `HM.member` hm
                          then return hm
                          else do
                            pr <- checkPost lrs ghci fc
                            return (HM.insert fc pr hm)) HM.empty fcs

checkPre :: (InfConfigM m, MonadIO m) => LiquidReadyState -> [GhcInfo] -> FuncCall -> m Bool
checkPre = checkPreOrPost (zeroOutKeys . ls_assumptions) arguments

checkPost :: (InfConfigM m, MonadIO m) => LiquidReadyState -> [GhcInfo] ->FuncCall -> m Bool
checkPost = checkPreOrPost (zeroOutKeys . ls_posts) (\fc -> arguments fc ++ [returns fc])

zeroOutKeys :: M.Map Name v -> M.Map Name v
zeroOutKeys = M.mapKeys (\(Name n m _ l) -> Name n m 0 l)

checkPreOrPost :: (InfConfigM m, MonadIO m)
               => (LiquidData -> M.Map Name Expr) -> (FuncCall -> [Expr]) -> LiquidReadyState -> [GhcInfo] -> FuncCall -> m Bool
checkPreOrPost extract ars lrs ghci cex@(FuncCall { funcName = Name n m _ _ }) = do
    config <- g2ConfigM
    let config' = config { counterfactual = NotCounterfactual }
    -- We use the same function to instantiate this state as in runLHInferenceCore, so all the names line up
    ld@(LiquidData
          { ls_state = s
          , ls_bindings = bindings }) <- liftIO $ processLiquidReadyStateWithCall lrs ghci n m config' mempty

    case checkFromMap ars (extract ld) cex s of
        Just s' -> do
            SomeSolver solver <- liftIO $ initSolver config
            (fsl, _) <- liftIO $ genericG2Call config' solver s' bindings
            liftIO $ close solver

            -- liftIO $ do
            --   print n
            --   print . curr_expr $ s'
            --   mapM_ (print . curr_expr . final_state) fsl

            -- We may return multiple states if any of the specifications contained a SymGen
            return $ any (currExprIsTrue . final_state) fsl
        -- If there is no explicit specification, the specification is implicitly True
        Nothing -> return True

checkFromMap :: (FuncCall -> [Expr]) -> M.Map Name Expr -> FuncCall -> State t -> Maybe (State t)
checkFromMap ars specs fc@(FuncCall { funcName = n }) s@(State { expr_env = eenv, known_values = kv }) =
    let
        e = M.lookup n specs
    in
    case e of
        Just e' ->
            let
                e'' = mkApp $ e':ars fc
            in
            Just $ s { curr_expr = CurrExpr Evaluate e''
                     , true_assert = True }
        Nothing -> Nothing

-------------------------------
-- Eval Measures
-------------------------------
-- Evaluate all relevant measures on a given expression

-- type MeasureExs = GMeasureExs Expr
-- type GMeasureExs e = HM.HashMap Name (HS.HashSet (GMeasureEx e))


-- type MeasureEx = GMeasureEx Expr
-- data GMeasureEx e = MeasureEx { meas_in :: e
--                               , meas_out :: e }
--                               deriving (Show, Read, Eq, Generic, Typeable, Data)

-- instance Hashable e => Hashable (GMeasureEx e)

type MeasureExs = HM.HashMap Expr [(Name, Expr)]

evalMeasures :: (InfConfigM m, MonadIO m) => LiquidReadyState -> [GhcInfo] -> [Expr] -> m MeasureExs
evalMeasures lrs ghci es = do
    config <- g2ConfigM
    liftIO $ do
        let config' = config { counterfactual = NotCounterfactual }

        let memc = emptyMemConfig { pres_func = presMeasureNames }
        LiquidData { ls_state = s
                   , ls_bindings = bindings
                   , ls_measures = meas
                   , ls_tcv = tcv
                   , ls_memconfig = pres_names } <- extractWithoutSpecs lrs (Id (Name "" Nothing 0 Nothing) TyUnknown) ghci config' memc

        let s' = s { true_assert = True }
            (final_s, final_b) = markAndSweepPreserving pres_names s' bindings

        SomeSolver solver <- initSolver config
        meas_res <- mapM (evalMeasures' final_s final_b solver config' meas tcv) $ filter (not . isError) es
        close solver

        return $ foldr (HM.unionWith (++)) HM.empty meas_res
    where
        meas_names = map (val . msName) $ measureSpecs ghci
        meas_nameOcc = map (\(Name n md _ _) -> (n, md)) $ map symbolName meas_names

        presMeasureNames s _ hs =
            let
                eenv = E.filterWithKey (\(Name n md _ _) _ -> (n, md) `elem` meas_nameOcc) (expr_env s)
                eenv_meas_names = E.keys eenv
            in
            foldr HS.insert hs eenv_meas_names
    
        isError (Prim Error _) = True
        isError _ = False

evalMeasures' :: ( ASTContainer t Expr
                 , ASTContainer t Type
                 , Named t
                 , Solver solver
                 , Show t) => State t -> Bindings -> solver -> Config -> Measures -> TCValues -> Expr -> IO MeasureExs
evalMeasures' s bindings solver config meas tcv e =  do
    let m_sts = evalMeasures'' s bindings meas tcv e

    m_sts' <- mapM (\(n, e_in, s_meas) -> do
        (er, _) <- genericG2Call config solver s_meas bindings
        case er of
            [er'] -> 
                let 
                    CurrExpr _ e_out = curr_expr . final_state $ er'
                in
                return (e_in, [(n, e_out)])
            [] -> return (e_in, [(n, Prim Undefined TyBottom)])
            _ -> error "evalMeasures': Bad G2 Call") m_sts

    return $ foldr (uncurry (HM.insertWith (++))) HM.empty  m_sts'

evalMeasures'' :: State t -> Bindings -> Measures -> TCValues -> Expr -> [(Name, Expr, State t)]
evalMeasures'' s b m tcv e =
    let
        rel_m = mapMaybe (\(n, me) ->
                              let
                                  t_me = typeOf $ me
                                  ret_t = returnType $ PresType t_me
                              in
                              case filter notLH . argumentTypes . PresType . inTyForAlls $ t_me of
                                  [t] ->
                                      case typeOf e `specializes` t of
                                          (True, bound) -> Just (n, me, bound)
                                          _ -> Nothing
                                  at -> Nothing) $ E.toExprList m
    in
    map (\(n, me, bound) ->
            let
                i = Id n (typeOf me)
                str_call = evalMeasuresCE b i e bound
            in
            (n, e, s { curr_expr = CurrExpr Evaluate str_call })
        ) rel_m
    where
        notLH t
            | TyCon n _ <- tyAppCenter t = n /= lhTC tcv
            | otherwise = False

evalMeasuresCE :: Bindings -> Id -> Expr -> M.Map Name Type -> Expr
evalMeasuresCE bindings i e bound =
    let
        bound_names = map idName $ tyForAllBindings i
        bound_tys = map (\n -> case M.lookup n bound of
                                Just t -> t
                                Nothing -> error $ "Bound type not found" ++ "\n" ++ show n ++ "\ne = " ++ show e) bound_names

        lh_dicts = map (const $ Prim Undefined TyBottom) bound_tys
        ds = deepseq_walkers bindings

        call =  mkApp $ Var i:map Type bound_tys ++ lh_dicts ++ [e]
        str_call = maybe call (fillLHDictArgs ds) $ mkStrict_maybe ds call
    in
    str_call

-------------------------------
-- Generic
-------------------------------
genericG2Call :: ( ASTContainer t Expr
                 , ASTContainer t Type
                 , Named t
                 , Solver solver) => Config -> solver -> State t -> Bindings -> IO ([ExecRes t], Bindings)
genericG2Call config solver s bindings = do
    let simplifier = ADTSimplifier arbValue
        share = sharing config

    fslb <- runG2WithSomes (SomeReducer (StdRed share solver simplifier))
                           (SomeHalter SWHNFHalter)
                           (SomeOrderer NextOrderer)
                           solver simplifier emptyMemConfig s bindings

    return fslb

genericG2CallLogging :: ( ASTContainer t Expr
                        , ASTContainer t Type
                        , Named t
                        , Show t
                        , Solver solver) => Config -> solver -> State t -> Bindings -> String -> IO ([ExecRes t], Bindings)
genericG2CallLogging config solver s bindings log = do
    let simplifier = ADTSimplifier arbValue
        share = sharing config

    fslb <- runG2WithSomes (SomeReducer (StdRed share solver simplifier :<~ Logger log))
                           (SomeHalter SWHNFHalter)
                           (SomeOrderer NextOrderer)
                           solver simplifier emptyMemConfig s bindings

    return fslb
