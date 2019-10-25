{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module G2.Liquid.Inference.G2Calls ( MeasureExs
                                   , MeasureEx (..)
                                   , checkCounterexample
                                   , evalMeasures) where

import G2.Config

import G2.Execution
import G2.Interface
import G2.Language
import qualified G2.Language.ExprEnv as E
import G2.Language.KnownValues
import G2.Liquid.Conversion
import G2.Liquid.Helpers
import G2.Liquid.Interface
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

import Debug.Trace

-------------------------------
-- Checking Counterexamples
-------------------------------
-- Does a given (counter)example violate a specification?
-- This allows us to check if a found counterexample violates a user-provided specifications,
-- or a synthesized specification

checkCounterexample :: (Maybe T.Text, ExtractedG2) -> [GhcInfo] -> Config -> FuncCall -> IO Bool
checkCounterexample exg2 ghci config cex@(FuncCall {funcName = n}) = do
    let config' = config { counterfactual = NotCounterfactual }
    (_, _, s, bindings, _, _, _) <- liquidState (nameOcc n) exg2 ghci config' mempty

    let s' = checkCounterexample' cex s

    (fsl, _) <- genericG2Call config' s' bindings

    case fsl of
        [ExecRes
            {
                final_state = fs@(State { curr_expr = CurrExpr _ (Data (DataCon (Name n _ _ _) _))})
            }] ->
            return $ n == "True"
        _ -> error $ "checkCounterexample: Bad return from runG2WithSomes" ++ show (curr_expr . final_state . head $ fsl)

checkCounterexample' :: FuncCall -> State t -> State t
checkCounterexample' fc@(FuncCall { funcName = n }) s@(State { expr_env = eenv })
    | Just e <- E.lookup n eenv =
    let
        e' = toJustSpec fc (leadingLamIds e) (inLams e)
    in
    s { curr_expr = CurrExpr Evaluate e'
      , true_assert = True }

toJustSpec :: FuncCall -> [Id] -> Expr -> Expr
toJustSpec (FuncCall { funcName = n, arguments = ars, returns = ret }) is (Let [(b, _)] (Assert _ e _)) =
    let
        rep = (Var b, ret):zip (map Var is) ars  
    in
    foldr (uncurry replaceASTs) e rep
toJustSpec _ _ _ = error "toJustSpec: ill-formed state"

-------------------------------
-- Eval Measures
-------------------------------
-- Evaluate all relevant measures on a given expression

type MeasureExs = HM.HashMap Name (HS.HashSet MeasureEx)
data MeasureEx = MeasureEx { meas_in :: Expr
                           , meas_out :: Expr }
                           deriving (Show, Read, Eq, Generic, Typeable, Data)

instance Hashable MeasureEx

evalMeasures :: (Maybe T.Text, ExtractedG2) -> [GhcInfo] -> Config -> [Expr] -> IO MeasureExs
evalMeasures exg2 ghci config es = do
    let config' = config { counterfactual = NotCounterfactual }
        arb_i = nameOcc . idName . fst . head . exg2_binds . snd $ exg2

    (_, _, s, bindings, meas, tcv, _) <- liquidState arb_i exg2 ghci config' (emptyMemConfig { pres_func = presMeasureNames })

    let s' = s { true_assert = True }

    return . foldr (HM.unionWith HS.union) HM.empty =<< mapM (evalMeasures' meas_names s' bindings config' meas tcv) es
    where
        meas_names = map (val . name) $ measureSpecs ghci
        meas_nameOcc = map (\(Name n md _ _) -> (n, md)) $ map symbolName meas_names

        presMeasureNames s b hs =
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

    m_sts' <- mapM (\(n, e_in, s_meas) -> do
        (er, _) <- genericG2Call config s_meas bindings
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

        t = typeOf e

        filtered_m = E.filterWithKey (\(Name n md _ _) _ -> (n, md) `elem` meas_nameOcc) m
        rel_m = mapMaybe (\(n, me) -> case filter notLH . argumentTypes . PresType . inTyForAlls . typeOf $ me of
                                        [t] ->
                                            case typeOf e `specializes` t of
                                                (True, bound) -> Just (n, me, bound)
                                                _ -> Nothing
                                        at -> Nothing) $ E.toExprList filtered_m
    in
    trace ("meas_nameOcc = " ++ show meas_nameOcc ++ "\bE.keys filtered_m = " ++ show (E.keys filtered_m))
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
        str_call = fillLHDictArgs ds $ mkStrict ds call
    in
    str_call

-------------------------------
-- Generic
-------------------------------
genericG2Call :: ( ASTContainer t Expr
                 , ASTContainer t Type
                 , Named t) => Config -> State t -> Bindings -> IO ([ExecRes t], Bindings)
genericG2Call config s bindings = do
    SomeSolver solver <- initSolver config
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
                        , Named t) => Config -> State t -> Bindings -> IO ([ExecRes t], Bindings)
genericG2CallLogging config s bindings = do
    SomeSolver solver <- initSolver config
    let simplifier = ADTSimplifier arbValue
        share = sharing config

    fslb <- runG2WithSomes (SomeReducer (StdRed share solver simplifier :<~ Logger "error2"))
                           (SomeHalter SWHNFHalter)
                           (SomeOrderer NextOrderer)
                           solver simplifier emptyMemConfig s bindings

    close solver

    return fslb
