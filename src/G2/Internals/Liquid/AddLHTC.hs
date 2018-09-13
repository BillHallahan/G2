{-# LANGUAGE OverloadedStrings #-}

module G2.Internals.Liquid.AddLHTC (addLHTC) where

import G2.Internals.Language
import G2.Internals.Language.Monad
import G2.Internals.Liquid.Types

import G2.Internals.Liquid.Conversion2

import qualified Data.Map as M

import Debug.Trace

addLHTC :: LHStateM ()
addLHTC = mapME addLHTCExprEnv

addLHTCExprEnv :: Expr -> LHStateM Expr
addLHTCExprEnv e = do
    (e', m) <- addLHTCExprEnvLams [] e
    addLHTCExprEnvPasses m e'

-- Updates a function definition with Lambdas to take the LH TC for each type argument.
addLHTCExprEnvLams :: [Id] -> Expr -> LHStateM (Expr, M.Map Name Id)
addLHTCExprEnvLams is (Lam TypeL i e) = do
    (e', m) <- addLHTCExprEnvLams (i:is) e
    return (Lam TypeL i e', m)
addLHTCExprEnvLams is e = do
    lh <- lhTCM

    let is' = reverse is
    let is'' = map (TyApp (TyConApp lh (TyApp TYPE TYPE)) . TyVar) $ is'
    is''' <- freshIdsN is''

    let e' = foldr (Lam TermL) e is'''

    let m = M.fromList $ zip (map idName is') is'''

    return (e', m)

-- Updates each function call, so that it is passed the appropriate LH TC.
-- This requires both:
-- (1) Modify the expression, to pass the appropriate arguments
-- (2) Modifying the type of the function variable
addLHTCExprEnvPasses :: M.Map Name Id -> Expr -> LHStateM Expr
addLHTCExprEnvPasses m e =
    modifyAppTopE (addLHTCExprEnvPasses' m) =<< addLHDictToTypes m e

addLHTCExprEnvPasses' :: M.Map Name Id -> Expr -> LHStateM Expr
addLHTCExprEnvPasses' m a@(App _ _) = do
    let a' = unApp a
    
    a'' <- addLHTCExprEnvPasses'' m [] a'
    return $ mkApp a''
addLHTCExprEnvPasses' _ e = return e

addLHTCExprEnvPasses'' :: M.Map Name Id -> [Expr] -> [Expr] -> LHStateM [Expr]
addLHTCExprEnvPasses'' _ es [] = return $ reverse es
addLHTCExprEnvPasses'' m es (te@(Type t):es') = do
    dict <- lookupLHDict m t
    as <- addLHTCExprEnvPasses'' m (dict:es) es'
    return $ te:as
addLHTCExprEnvPasses'' m es (e:es') = do
    as <- addLHTCExprEnvPasses'' m [] es'
    return $ reverse es ++ e:as

lookupLHDict :: M.Map Name Id -> Type -> LHStateM Expr
lookupLHDict m (TyVar (Id n _)) =
    case M.lookup n m of 
        Just e -> return $ Var e
        Nothing -> return $ Var (Id (Name "BAD 1" Nothing 0 Nothing) TyUnknown) -- error "No LH Dict in lookupLHDict 1"
lookupLHDict _ t = do
        lh <- lhTCM
        dict <- lookupTCDictTC lh t
        case dict of
            Just i -> return $ Var i
            Nothing -> return $ Var (Id (Name "BAD 2" Nothing 0 Nothing) TyUnknown) -- error $ "No LH Dict in lookupLHDict 2" ++ show t