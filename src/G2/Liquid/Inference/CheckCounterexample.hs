{-# LANGUAGE OverloadedStrings #-}

module G2.Liquid.Inference.CheckCounterexample (checkCounterexample) where

import G2.Config

import G2.Execution
import G2.Interface
import G2.Language
import qualified G2.Language.ExprEnv as E
import G2.Language.KnownValues
import G2.Liquid.Interface
import G2.Liquid.Types
import G2.Solver hiding (Assert)
import G2.Translation

import Language.Haskell.Liquid.Types hiding (Config)

import qualified Data.Text as T

checkCounterexample :: (Maybe T.Text, ExtractedG2) -> [GhcInfo] -> Config -> FuncCall -> IO Bool
checkCounterexample exg2 ghci config cex@(FuncCall {funcName = n}) = do
    let config' = config { counterfactual = NotCounterfactual }
    (_, _, s, bindings, _) <- liquidState (nameOcc n) exg2 ghci config'

    let s' = checkCounterexample' cex s

    SomeSolver solver <- initSolver config
    let simplifier = ADTSimplifier arbValue
        share = sharing config

    (fsl, b) <- runG2WithSomes (SomeReducer (StdRed share solver simplifier ))
                              (SomeHalter SWHNFHalter)
                              (SomeOrderer NextOrderer)
                              solver simplifier emptyMemConfig s' bindings

    close solver

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
