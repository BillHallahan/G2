{-# LANGUAGE OverloadedStrings #-}

module G2.Internals.Liquid.AddLHTC (addLHTC) where

import G2.Internals.Language
import G2.Internals.Language.Monad
import G2.Internals.Liquid.Types

import G2.Internals.Liquid.Conversion2

import qualified Data.Map as M

import Debug.Trace

addLHTC :: LHStateM ()
addLHTC = do
    mapME addLHTCExprEnv

    (CurrExpr er ce) <- currExpr
    ce' <- addLHTCExprPasses M.empty ce
    putCurrExpr (CurrExpr er ce')

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
    addLHTCExprPasses m =<< addLHDictToTypes m e

-- We only want to pass the LH TC to Var's (aka function calls)
-- We DO NOT want to put it in DataCons
addLHTCExprPasses :: M.Map Name Id -> Expr -> LHStateM Expr
addLHTCExprPasses m = modifyAppTopE (addLHTCExprPasses' m)

addLHTCExprPasses' :: M.Map Name Id -> Expr -> LHStateM Expr
addLHTCExprPasses' m a@(App _ _)
    | (Var _:_) <- a' = do
        a'' <- addLHTCExprPasses'' m [] a'
        return $ mkApp a''
    | otherwise = return a
    where
        a' = unApp a
addLHTCExprPasses' _ e = return e

addLHTCExprPasses'' :: M.Map Name Id -> [Expr] -> [Expr] -> LHStateM [Expr]
addLHTCExprPasses'' _ es [] = return $ reverse es
addLHTCExprPasses'' m es (te@(Type t):es') = do
    dict <- lhTCDict m t
    as <- addLHTCExprPasses'' m (dict:es) es'
    return $ te:as
addLHTCExprPasses'' m es (e:es')
    | Var (Id n _) <- e
    , Just dict <- M.lookup n m = do
        as <- addLHTCExprPasses'' m (Var dict:es) es'
        return $ e:as
    | otherwise = do
        as <- addLHTCExprPasses'' m [] es'
        return $ reverse es ++ e:as

lhTCDict :: M.Map Name Id -> Type -> LHStateM Expr
lhTCDict m t = do
    lh <- lhTCM
    tc <- typeClassInstTC m lh t
    case tc of
        Just e -> return $ dropAppedLH e
        Nothing -> return $ Var (Id (Name "BAD 2" Nothing 0 Nothing) TyUnknown)
    where
        -- typeClassInstTC adds any needed LH Dict arguments for us.
        -- Unfortunately, the LH Dicts are then added AGAIN, by addLHTCExprEnvPasses
        -- So we just drop the LH Dicts added by typeClassInstTC, and everything works out
        dropAppedLH :: Expr -> Expr
        dropAppedLH (App e t@(Type _)) = App (dropAppedLH e) t
        dropAppedLH (App e _) = dropAppedLH e
        dropAppedLH e = e