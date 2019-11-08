{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}

module G2.Liquid.Inference.G2Calls ( MeasureExs
                                   , GMeasureExs
                                   , MeasureEx
                                   , GMeasureEx (..)
                                   , runLHInferenceCore
                                   , checkCounterexample
                                   , evalMeasures) where

import G2.Config

import G2.Execution
import qualified G2.Initialization.Types as IT
import G2.Interface
import G2.Language
import qualified G2.Language.ExprEnv as E
import G2.Liquid.Conversion
import G2.Liquid.Helpers
import G2.Liquid.Interface
import G2.Liquid.LHReducers
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

-------------------------------
-- Generating Counterexamples
-------------------------------
runLHInferenceCore :: T.Text
                   -> Maybe T.Text
                   -> LiquidReadyState
                   -> [GhcInfo]
                   -> Config
                   -> IO (([ExecRes [Abstracted]], Bindings), Id)
runLHInferenceCore entry m lrs ghci config = do
    LiquidData { ls_state = final_st
               , ls_bindings = bindings
               , ls_id = ifi
               , ls_counterfactual_name = cfn
               , ls_memconfig = pres_names } <- processLiquidReadyStateWithCall lrs ghci entry m config mempty

    SomeSolver solver <- initSolver config
    let simplifier = ADTSimplifier arbValue

    (red, hal, ord) <- inferenceReducerHalterOrderer config solver simplifier entry m cfn final_st
    (exec_res, final_bindings) <- runLHG2 config red hal ord solver simplifier pres_names final_st bindings

    close solver

    return ((exec_res, final_bindings), ifi)

inferenceReducerHalterOrderer :: (Solver solver, Simplifier simplifier)
                              => Config
                              -> solver
                              -> simplifier
                              -> T.Text
                              -> Maybe T.Text
                              -> Name
                              -> State t
                              -> IO (SomeReducer LHTracker, SomeHalter LHTracker, SomeOrderer LHTracker)
inferenceReducerHalterOrderer config solver simplifier entry mb_modname cfn st = do
    let
        ng = mkNameGen ()

        share = sharing config

        (limHalt, limOrd) = limitByAccepted (cut_off config)
        state_name = Name "state" Nothing 0 Nothing

        searched_below = SearchedBelowHalter { found_at_least = 3
                                             , discarded_at_least = 6
                                             , discarded_at_most = 15 }
    
    timer_halter <- timerHalter 10

    return $ if higherOrderSolver config == AllFuncs then 
        ( SomeReducer NonRedPCRed
            <~| (case logStates config of
                  Just fp -> SomeReducer (StdRed share solver simplifier :<~| LHRed cfn :<~ Logger fp)
                  Nothing -> SomeReducer (StdRed share solver simplifier :<~| LHRed cfn))
        , SomeHalter
                (MaxOutputsHalter (maxOutputs config)
                  :<~> LHAbsHalter entry mb_modname (expr_env st)
                  :<~> searched_below
                  :<~> SwitchEveryNHalter (switch_after config)
                  :<~> AcceptHalter
                  :<~> timer_halter)
        , SomeOrderer LHLimitByAcceptedOrderer)
    else
        (SomeReducer (NonRedPCRed :<~| TaggerRed state_name ng)
            <~| (case logStates config of
                  Just fp -> SomeReducer (StdRed share solver simplifier :<~| LHRed cfn :<~ Logger fp)
                  Nothing -> SomeReducer (StdRed share solver simplifier :<~| LHRed cfn))
        , SomeHalter
            (DiscardIfAcceptedTag state_name
              :<~> MaxOutputsHalter (maxOutputs config)
              :<~> LHAbsHalter entry mb_modname (expr_env st)
              :<~> searched_below
              :<~> SwitchEveryNHalter (switch_after config)
              :<~> AcceptHalter
              :<~> timer_halter)
        , SomeOrderer LHLimitByAcceptedOrderer)

-------------------------------
-- Checking Counterexamples
-------------------------------
-- Does a given (counter)example violate a specification?
-- This allows us to check if a found counterexample violates a user-provided specifications,
-- or a synthesized specification
checkCounterexample :: LiquidReadyState -> [GhcInfo] -> Config -> FuncCall -> IO Bool
checkCounterexample lrs ghci config cex@(FuncCall { funcName = Name n m _ _ }) = do
    let config' = config { counterfactual = NotCounterfactual }
    -- We use the same function to instantiate this state as in runLHInferenceCore, so all the names line up
    LiquidData { ls_state = s
               , ls_bindings = bindings } <- processLiquidReadyStateWithCall lrs ghci n m config' mempty

    let s' = checkCounterexample' cex s

    SomeSolver solver <- initSolver config
    (fsl, _) <- genericG2Call config' solver s' bindings

    case fsl of
        [ExecRes
            {
                final_state = (State { curr_expr = CurrExpr _ (Data (DataCon (Name dcn _ _ _) _))})
            }] ->
            return $ dcn == "True"
        _ -> error $ "checkCounterexample: Bad return from runG2WithSomes" ++ show (curr_expr . final_state . head $ fsl)

checkCounterexample' :: FuncCall -> State t -> State t
checkCounterexample' fc@(FuncCall { funcName = n }) s@(State { expr_env = eenv })
    | Just e <- E.lookup n eenv =
    let
        e' = toJustSpec fc (leadingLamIds e) (inLams e)
    in
    s { curr_expr = CurrExpr Evaluate e'
      , true_assert = True }
    | otherwise = error $ "checkCounterexample': Name not found " ++ show n

toJustSpec :: FuncCall -> [Id] -> Expr -> Expr
toJustSpec (FuncCall { arguments = ars, returns = ret }) is (Let [(b, _)] (Assert _ e _)) =
    let
        rep = (Var b, ret):zip (map Var is) ars  
    in
    foldr (uncurry replaceASTs) e rep
toJustSpec _ _ _ = error "toJustSpec: ill-formed state"

-------------------------------
-- Eval Measures
-------------------------------
-- Evaluate all relevant measures on a given expression

type MeasureExs = GMeasureExs Expr
type GMeasureExs e = HM.HashMap Name (HS.HashSet (GMeasureEx e))


type MeasureEx = GMeasureEx Expr
data GMeasureEx e = MeasureEx { meas_in :: e
                              , meas_out :: e }
                              deriving (Show, Read, Eq, Generic, Typeable, Data)

instance Hashable e => Hashable (GMeasureEx e)

instance AST e => ASTContainer (GMeasureEx e) e where
    containedASTs (MeasureEx { meas_in = m_in, meas_out = m_out }) = [m_in, m_out]
    modifyContainedASTs f (MeasureEx { meas_in = m_in, meas_out = m_out }) =
        MeasureEx { meas_in = f m_in, meas_out = f m_out }

evalMeasures :: LiquidReadyState -> [GhcInfo] -> Config -> [Expr] -> IO MeasureExs
evalMeasures lrs ghci config es = do
    let config' = config { counterfactual = NotCounterfactual }

    let memc = emptyMemConfig { pres_func = presMeasureNames }
    LiquidData { ls_state = s
               , ls_bindings = bindings
               , ls_measures = meas
               , ls_tcv = tcv
               , ls_memconfig = pres_names } <- extractWithoutSpecs lrs (Id (Name "" Nothing 0 Nothing) TyUnknown) ghci config' memc

    putStrLn $ "meas_nameOcc = " ++ show meas_nameOcc
    putStrLn $ "res = " ++ show (pres_func memc s bindings HS.empty)

    let s' = s { true_assert = True }
        (final_s, final_b) = markAndSweepPreserving pres_names s' bindings

    return . foldr (HM.unionWith HS.union) HM.empty =<< mapM (evalMeasures' meas_names final_s final_b config' meas tcv) es
    where
        meas_names = map (val . name) $ measureSpecs ghci
        meas_nameOcc = map (\(Name n md _ _) -> (n, md)) $ map symbolName meas_names

        presMeasureNames s _ hs =
            let
                eenv = E.filterWithKey (\(Name n md _ _) _ -> (n, md) `elem` meas_nameOcc) (expr_env s)
                eenv_meas_names = E.keys eenv
            in
            foldr HS.insert hs eenv_meas_names

evalMeasures' :: ( ASTContainer t Expr
                 , ASTContainer t Type
                 , Named t) => [Symbol] -> State t -> Bindings -> Config -> Measures -> TCValues -> Expr -> IO MeasureExs
evalMeasures' meas_names s bindings config meas tcv e =  do
    let m_sts = evalMeasures'' meas_names s bindings meas tcv e

    SomeSolver solver <- initSolver config

    m_sts' <- mapM (\(n, e_in, s_meas) -> do
        (er, _) <- genericG2Call config solver s_meas bindings
        case er of
            [er'] -> 
                let 
                    CurrExpr _ e_out = curr_expr . final_state $ er'
                in
                return (n, MeasureEx { meas_in = e_in, meas_out = e_out })
            [] -> return (n, MeasureEx { meas_in = e_in, meas_out = Prim Undefined TyBottom })
            _ -> error "evalMeasures': Bad G2 Call") m_sts

    return $ foldr (uncurry (HM.insertWith HS.union)) HM.empty
                        $ map (\(n, ee) -> (n, HS.singleton ee)) m_sts'

evalMeasures'' :: [Symbol] -> State t -> Bindings -> Measures -> TCValues -> Expr -> [(Name, Expr, State t)]
evalMeasures'' meas_names s b m tcv e =
    let
        meas_nameOcc = map (\(Name n md _ _) -> (n, md)) $ map symbolName meas_names

        filtered_m = E.filterWithKey (\(Name n md i _) _ -> (n, md) `elem` meas_nameOcc && i == 0) m
        rel_m = mapMaybe (\(n, me) -> case filter notLH . argumentTypes . PresType . inTyForAlls . typeOf $ me of
                                        [t] ->
                                            case typeOf e `specializes` t of
                                                (True, bound) -> Just (n, me, bound)
                                                _ -> Nothing
                                        at -> Nothing) $ E.toExprList filtered_m
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
                                Nothing -> error "Bound type not found") bound_names

        lh_dicts = map (const $ Prim Undefined TyBottom) bound_tys
        ds = deepseq_walkers bindings

        call =  mkApp $ Var i:map Type bound_tys ++ lh_dicts ++ [e]
        str_call = maybe call (fillLHDictArgs ds) $ mkStrict_maybe ds call -- fillLHDictArgs ds $ mkStrict ds call
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

    fslb <- runG2WithSomes (SomeReducer (StdRed share solver simplifier ))
                           (SomeHalter SWHNFHalter)
                           (SomeOrderer NextOrderer)
                           solver simplifier emptyMemConfig s bindings

    close solver

    return fslb

genericG2CallLogging :: ( ASTContainer t Expr
                        , ASTContainer t Type
                        , Named t
                        , Solver solver) => Config -> solver -> State t -> Bindings -> IO ([ExecRes t], Bindings)
genericG2CallLogging config solver s bindings = do
    let simplifier = ADTSimplifier arbValue
        share = sharing config

    fslb <- runG2WithSomes (SomeReducer (StdRed share solver simplifier :<~ LimLogger 0 0 [] "aMeasures"))
                           (SomeHalter SWHNFHalter)
                           (SomeOrderer NextOrderer)
                           solver simplifier emptyMemConfig s bindings

    close solver

    return fslb
