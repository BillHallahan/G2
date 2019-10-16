{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module G2.Liquid.ReduceAbstracted (reduceAbstracted) where

import G2.Config
import G2.Execution
import G2.Interface
import G2.Language
import qualified G2.Language.ExprEnv as E
import G2.Liquid.LHReducers
import G2.Solver

import G2.Lib.Printers

import Debug.Trace

reduceAbstracted :: Config -> Bindings -> ExecRes LHTracker -> IO (ExecRes LHTracker)
reduceAbstracted config bindings
                er@(ExecRes { final_state = (s@State { track = lht}) }) = do
    let fcs = abstract_calls lht

    SomeSolver solver <- initSolver config
    let simplifier = ADTSimplifier arbValue
        share = sharing config

    fcs' <- mapM (reduceFuncCall share solver simplifier s bindings) fcs

    close solver

    return er { final_state = s { track = lht { abstract_calls = fcs' } }}

reduceFuncCall :: (Solver solver, Simplifier simp) => Sharing -> solver -> simp -> State LHTracker -> Bindings -> FuncCall -> IO FuncCall
reduceFuncCall share solver simplifier s bindings fc@(FuncCall { arguments = ars }) = do
    red_ars <- mapM (\a ->
        if not . isTypeClass (type_classes s) $ (typeOf a)
            then do
                let a' = fmap fillLHDictArgs $ mkStrict_maybe (deepseq_walkers bindings) a
                case a' of
                    Just a' -> do
                        let s' = pickHead $
                                   s { expr_env = model s `E.union'` expr_env s
                                   , curr_expr = CurrExpr Evaluate  a'}
                       
                        (er, _) <- runG2WithSomes 
                                    (SomeReducer (StdRed share solver simplifier))
                                    (SomeHalter SWHNFHalter)
                                    (SomeOrderer NextOrderer)
                                    solver simplifier emptyMemConfig s' bindings

                        case er of
                            [er'] -> do
                                let (CurrExpr _ a'') = curr_expr . final_state $ er'
                                return a''
                            _ -> error "reduceAbstracted: Bad reduction"
                    Nothing -> return a
            else return a ) ars

    return fc { arguments = red_ars }

-- The walk function takes lhDict arguments that are not correctly accounted for by mkStrict.
-- The arguments are not actually used, so, here, we fill them in with undefined. 
fillLHDictArgs ::Expr -> Expr
fillLHDictArgs = modifyAppTop fillLHDictArgs'

fillLHDictArgs' :: Expr -> Expr
fillLHDictArgs' e
    | f@(Var _):xs <- unApp e = mkApp $ f:fillLHDictArgs'' 0 xs
    | otherwise = e

fillLHDictArgs'' :: Int -> [Expr] -> [Expr]
fillLHDictArgs'' !n [] = replicate n (Prim Undefined TyBottom)
fillLHDictArgs'' !n (t@(Type _):xs) = t:fillLHDictArgs'' (n + 1) xs
fillLHDictArgs'' !n xs = replicate n (Prim Undefined TyBottom) ++ xs

pickHead :: (ASTContainer m Expr) => m -> m
pickHead = modifyASTs pickHead'

pickHead' :: Expr -> Expr
pickHead' (NonDet xs) = head xs
pickHead' e = e