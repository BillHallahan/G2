{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module G2.Liquid.ReduceCalls (reduceCalls) where

import G2.Config
import G2.Execution
import G2.Interface
import G2.Language as G2
import qualified G2.Language.ExprEnv as E
import G2.Liquid.LHReducers
import G2.Solver

import G2.Lib.Printers

import qualified Data.Map as M

reduceCalls :: Config -> Bindings -> ExecRes LHTracker -> IO (ExecRes LHTracker)
reduceCalls config bindings er = do
    SomeSolver solver <- initSolver config
    let simplifier = ADTSimplifier arbValue

    er' <- reduceViolated solver simplifier (sharing config) bindings er
    er'' <- reduceAbstracted solver simplifier (sharing config) bindings er'

    close solver

    return er''

reduceViolated :: (Solver solver, Simplifier simplifier) => solver -> simplifier -> Sharing -> Bindings -> ExecRes LHTracker -> IO (ExecRes LHTracker)
reduceViolated solver simplifier share bindings er@(ExecRes { final_state = s, violated = Just v }) = do
    v' <- reduceFuncCall share solver simplifier s bindings v
    -- putStrLn $ "v = " ++ show v
    -- putStrLn $ "v' = " ++ show v'
    return er { violated = Just v' }
reduceViolated _ _ _ _ er = return er 

reduceAbstracted :: (Solver solver, Simplifier simplifier) => solver -> simplifier -> Sharing -> Bindings -> ExecRes LHTracker -> IO (ExecRes LHTracker)
reduceAbstracted solver simplifier share bindings
                er@(ExecRes { final_state = (s@State { track = lht}) }) = do
    let fcs = abstract_calls lht

    fcs' <- mapM (reduceFuncCall share solver simplifier s bindings) fcs

    return er { final_state = s { track = lht { abstract_calls = fcs' } }}

reduceFuncCall :: (Solver solver, Simplifier simp) => Sharing -> solver -> simp -> State LHTracker -> Bindings -> FuncCall -> IO FuncCall
reduceFuncCall share solver simplifier s bindings fc@(FuncCall { arguments = ars, returns = r }) = do
    red_ars <- mapM (reduceFCExpr share (SomeReducer (StdRed share solver simplifier)) solver simplifier s bindings) ars
    red_r <- reduceFCExpr share (SomeReducer (StdRed share solver simplifier)) solver simplifier s bindings r

    return fc { arguments = red_ars, returns = red_r }

reduceFCExpr :: (Solver solver, Simplifier simp) => Sharing -> SomeReducer LHTracker ->  solver -> simp -> State LHTracker -> Bindings -> Expr -> IO Expr
reduceFCExpr share reducer solver simplifier s bindings e 
    | not . isTypeClass (type_classes s) $ (typeOf e) = do
        let ds = deepseq_walkers bindings
            e' = maybe e (fillLHDictArgs ds) $ mkStrict_maybe ds e

        let s' = elimAsserts . pickHead $
                   s { expr_env = model s `E.union'` expr_env s
                   , curr_expr = CurrExpr Evaluate e'}

        (er, _) <- runG2WithSomes 
                    reducer
                    (SomeHalter SWHNFHalter)
                    (SomeOrderer NextOrderer)
                    solver simplifier emptyMemConfig s' bindings

        case er of
            [er'] -> do
                let (CurrExpr _ ce) = curr_expr . final_state $ er'
                return ce
            _ -> error "reduceAbstracted: Bad reduction"
    | otherwise = return e 

-- The walk function takes lhDict arguments that are not correctly accounted for by mkStrict.
-- The arguments are not actually used, so, here, we fill them in with undefined. 
fillLHDictArgs :: Walkers -> Expr -> Expr
fillLHDictArgs w = modifyAppTop (fillLHDictArgs' w)

fillLHDictArgs' :: Walkers -> Expr -> Expr
fillLHDictArgs' w e
    | f@(Var i):xs <- unApp e
    , any (\(_, i') -> i == i') (M.toList w) = mkApp $ f:fillLHDictArgs'' 0 xs
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