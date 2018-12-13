{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module G2.Liquid.AddLHTC ( addLHTC
                                   , addLHTCExprPasses ) where

import G2.Language
import G2.Language.Monad
import G2.Liquid.Types

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
    e' <- addTypeLams e
    e'' <- addTypeLamsLet e'
    (e''', m) <- addLHTCExprEnvLams [] e''
    addLHTCExprEnvPasses m e'''

-- Rewrites a type to make type lambdas explicit
-- This is needed so that addLHTCExprEnvLams can insert the LH Dict after the type correctly.
-- In generally, it's not always correct to eta-expand Haskell functions, but
-- it is fine here because the type arguments are guaranteed to not be undefined
addTypeLams :: Expr -> LHStateM Expr
addTypeLams e = 
    let
        t = typeOf e
    in
    addTypeLams' t e

addTypeLams' :: Type -> Expr -> LHStateM Expr
addTypeLams' (TyForAll _ t) (Lam TypeL i e) = return . Lam TypeL i =<< addTypeLams' t e
addTypeLams' (TyForAll (NamedTyBndr i) t) e =
    return . Lam TypeL i =<< addTypeLams' t (App e (Type (TyVar i)))
addTypeLams' _ e = return e

-- | Let bindings may be passed Type parameters, but have no type lambdas,
-- so we have to add Lambdas to Let's as well. 
addTypeLamsLet :: Expr -> LHStateM Expr
addTypeLamsLet = modifyM addTypeLamsLet'

addTypeLamsLet' :: Expr -> LHStateM Expr
addTypeLamsLet' (Let be e) = do
    be' <- mapM (\(b, e') -> do
            e'' <- addTypeLams e'
            return (b, e'')
        ) be
    return (Let be' e)
addTypeLamsLet' e = return e

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

    -- Lambdas may be nested in an Expr (for example, if the lambda is in a Let)
    -- So hear we dig down, and recursively apply addLHTCExprEnvLams to any
    -- nested Lambdas
    (le, m') <- addLHTCExprEnvNextLams e

    let e' = foldr (Lam TermL) le is'''

    let m = M.fromList $ zip (map idName is') is'''

    return (e', M.union m m')

addLHTCExprEnvNextLams :: Expr -> LHStateM (Expr, M.Map Name Id)
addLHTCExprEnvNextLams e@(Var _) = return (e, M.empty)
addLHTCExprEnvNextLams e@(Lit _) = return (e, M.empty)
addLHTCExprEnvNextLams e@(Prim _ _) = return (e, M.empty)
addLHTCExprEnvNextLams e@(Data _) = return (e, M.empty)
addLHTCExprEnvNextLams (App e1 e2) = do
    (e1', m1) <- addLHTCExprEnvNextLams e1
    (e2', m2) <- addLHTCExprEnvNextLams e2
    return (App e1' e2', M.union m1 m2)
addLHTCExprEnvNextLams e@(Lam TypeL _ _) = addLHTCExprEnvLams [] e
addLHTCExprEnvNextLams (Lam TermL i e) = do
    (e', m) <- addLHTCExprEnvNextLams e
    return (Lam TermL i e', m)
addLHTCExprEnvNextLams (Let b e) = do
    (b', ms) <- return . unzip =<< mapM (\(b', be) -> do
                                (be', m) <- addLHTCExprEnvNextLams be
                                return ((b', be'), m)
                            ) b
    (e', m) <- addLHTCExprEnvNextLams e

    return (Let b' e', foldr M.union M.empty (m:ms))
addLHTCExprEnvNextLams (Case e i a) = do
    (e', m) <- addLHTCExprEnvNextLams e

    (a', ms) <- return . unzip =<< mapM addLHTCExprEnvNextLamsAlt a

    return (Case e' i a', foldr M.union M.empty (m:ms))
addLHTCExprEnvNextLams e@(Type _) = return (e, M.empty)
addLHTCExprEnvNextLams (Cast e c) = do
    (e', m) <- addLHTCExprEnvNextLams e
    return (Cast e' c, m)
addLHTCExprEnvNextLams e@(Coercion _) = return (e, M.empty)
addLHTCExprEnvNextLams (Tick t e) = do
    (e', m) <- addLHTCExprEnvNextLams e
    return (Tick t e', m)
addLHTCExprEnvNextLams (NonDet es) = do
    (es', ms) <- return . unzip =<< mapM addLHTCExprEnvNextLams es
    return (NonDet es', foldr M.union M.empty ms)
addLHTCExprEnvNextLams e@(SymGen _) = return (e, M.empty)
addLHTCExprEnvNextLams (Assume fc e1 e2) = do
    (e1', m1) <- addLHTCExprEnvNextLams e1
    (e2', m2) <- addLHTCExprEnvNextLams e2
    return (Assume fc e1' e2', M.union m1 m2)
addLHTCExprEnvNextLams (Assert fc e1 e2) = do
    (e1', m1) <- addLHTCExprEnvNextLams e1
    (e2', m2) <- addLHTCExprEnvNextLams e2
    return (Assert fc e1' e2', M.union m1 m2)

addLHTCExprEnvNextLamsAlt :: Alt -> LHStateM (Alt, M.Map Name Id)
addLHTCExprEnvNextLamsAlt (Alt am e) = do
    (e', m) <- addLHTCExprEnvNextLams e
    return (Alt am e', m)

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
    | (Data _:_) <- unApp a  = return a
    | otherwise = do
        let a' = unApp a
        a'' <- addLHTCExprPasses'' m [] a'
        return $ mkApp a''

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
addLHDictToTypes''' m is t = do
    lh <- lhTCM
    let is' = reverse is
    let dictT = map (TyApp (TyCon lh (TyApp TYPE TYPE)) . TyVar) is'

    -- The recursive step in addLHDictToTypes'' only kicks in when it is not
    -- at a TyForAll.  So we have to perform recursion here, on the type nested
    -- in the TyForAll's
    t' <- addLHDictToTypes'' m t

    return $ foldr TyFun t' dictT

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
