{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module G2.Internals.Liquid.AddLHTC ( addLHTC ) where

import G2.Internals.Language
import G2.Internals.Language.Monad
import G2.Internals.Liquid.Types

import qualified Data.Map as M

-- | Adds the LiquidHaskell typeclass to all functions in the ExprEnv, and to
-- the current expression.  This requires:
--   1. Adding Lambda bindings for the LH TC
--   2. Passing the LH TC typeclass to functions
--   3. Updating all type information
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
    let is'' = map (TyApp (TyCon lh (TyApp TYPE TYPE)) . TyVar) $ is'
    is''' <- freshIdsN is''

    let e' = foldr (Lam TermL) e is'''

    let m = M.fromList $ zip (map idName is') is'''

    return (e', m)

-- Updates each function call, so that it is passed the appropriate LH TC.
-- This requires both:
-- (1) Modifying the expression, to pass the appropriate arguments
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
    | a'@(Var _:_) <- unApp a = do
        a'' <- addLHTCExprPasses'' m [] a'
        return $ mkApp a''

    | otherwise = return a

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

-- We want to add a LH Dict Type argument to Var's, but not DataCons or Lambdas.
-- That is: function calls need to be passed the LH Dict but it
-- doesn't need to be passed around in DataCons
addLHDictToTypes :: ASTContainerM e Expr => M.Map Name Id -> e -> LHStateM e
addLHDictToTypes m = modifyASTsM (addLHDictToTypes' m)

addLHDictToTypes' :: M.Map Name Id -> Expr -> LHStateM Expr
addLHDictToTypes' m (Var (Id n t)) = return . Var . Id n =<< addLHDictToTypes'' m t
addLHDictToTypes' _ e = return e

addLHDictToTypes'' :: M.Map Name Id -> Type -> LHStateM Type
addLHDictToTypes'' m t@(TyForAll (NamedTyBndr _) _) = addLHDictToTypes''' m [] t
addLHDictToTypes'' m t = modifyChildrenM (addLHDictToTypes'' m) t

addLHDictToTypes''' :: M.Map Name Id -> [Id] -> Type -> LHStateM Type
addLHDictToTypes''' m is (TyForAll (NamedTyBndr b) t) =
    return . TyForAll (NamedTyBndr b) =<< addLHDictToTypes''' m (b:is) t
addLHDictToTypes''' _ is t = do
    lh <- lhTCM
    let is' = reverse is
    let dictT = map (TyApp (TyCon lh (TyApp TYPE TYPE)) . TyVar) is'

    return $ foldr TyFun t dictT

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
        dropAppedLH (App e t'@(Type _)) = App (dropAppedLH e) t'
        dropAppedLH (App e _) = dropAppedLH e
        dropAppedLH e = e
