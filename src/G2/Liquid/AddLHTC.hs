{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module G2.Liquid.AddLHTC ( addLHTC
                         , addLHTCCurrExpr
                         , addLHTCExprPasses ) where

import G2.Language
import G2.Language.Monad
import G2.Liquid.Types

import qualified Data.HashMap.Lazy as HM

-- | Adds the LiquidHaskell typeclass to all functions in the ExprEnv, and to
-- the current expression.  This requires:
--   1. Adding Lambda bindings for the LH TC
--   2. Passing the LH TC typeclass to functions
--   3. Updating all type information
addLHTC :: LHStateM ()
addLHTC = do
    mapME addLHTCExprEnv
    addLHTCCurrExpr

addLHTCCurrExpr :: LHStateM ()
addLHTCCurrExpr = do
    (CurrExpr er ce) <- currExpr
    ce' <- addLHTCExprPasses HM.empty ce
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
addLHTCExprEnvLams :: [Id] -> Expr -> LHStateM (Expr, HM.HashMap Name Id)
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

    let m = HM.fromList $ zip (map idName is') is'''

    return (e', HM.union m m')

addLHTCExprEnvNextLams :: Expr -> LHStateM (Expr, HM.HashMap Name Id)
addLHTCExprEnvNextLams e@(Var _) = return (e, HM.empty)
addLHTCExprEnvNextLams e@(Lit _) = return (e, HM.empty)
addLHTCExprEnvNextLams e@(Prim _ _) = return (e, HM.empty)
addLHTCExprEnvNextLams e@(Data _) = return (e, HM.empty)
addLHTCExprEnvNextLams (App e1 e2) = do
    (e1', m1) <- addLHTCExprEnvNextLams e1
    (e2', m2) <- addLHTCExprEnvNextLams e2
    return (App e1' e2', HM.union m1 m2)
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

    return (Let b' e', foldr HM.union HM.empty (m:ms))
addLHTCExprEnvNextLams (Case e i t a) = do
    (e', m) <- addLHTCExprEnvNextLams e

    (a', ms) <- return . unzip =<< mapM addLHTCExprEnvNextLamsAlt a

    return (Case e' i t a', foldr HM.union HM.empty (m:ms))
addLHTCExprEnvNextLams e@(Type _) = return (e, HM.empty)
addLHTCExprEnvNextLams (Cast e c) = do
    (e', m) <- addLHTCExprEnvNextLams e
    return (Cast e' c, m)
addLHTCExprEnvNextLams e@(Coercion _) = return (e, HM.empty)
addLHTCExprEnvNextLams (Tick t e) = do
    (e', m) <- addLHTCExprEnvNextLams e
    return (Tick t e', m)
addLHTCExprEnvNextLams (NonDet es) = do
    (es', ms) <- return . unzip =<< mapM addLHTCExprEnvNextLams es
    return (NonDet es', foldr HM.union HM.empty ms)
addLHTCExprEnvNextLams e@(SymGen _) = return (e, HM.empty)
addLHTCExprEnvNextLams (Assume fc e1 e2) = do
    (e1', m1) <- addLHTCExprEnvNextLams e1
    (e2', m2) <- addLHTCExprEnvNextLams e2
    return (Assume fc e1' e2', HM.union m1 m2)
addLHTCExprEnvNextLams (Assert fc e1 e2) = do
    (e1', m1) <- addLHTCExprEnvNextLams e1
    (e2', m2) <- addLHTCExprEnvNextLams e2
    return (Assert fc e1' e2', HM.union m1 m2)

addLHTCExprEnvNextLamsAlt :: Alt -> LHStateM (Alt, HM.HashMap Name Id)
addLHTCExprEnvNextLamsAlt (Alt am e) = do
    (e', m) <- addLHTCExprEnvNextLams e
    return (Alt am e', m)

-- Updates each function call, so that it is passed the appropriate LH TC.
-- This requires both:
-- (1) Modifying the expression, to pass the appropriate arguments
-- (2) Modifying the type of the function variable
addLHTCExprEnvPasses :: HM.HashMap Name Id -> Expr -> LHStateM Expr
addLHTCExprEnvPasses m e =
    addLHTCExprPasses m =<< addLHDictToTypes m e

-- We only want to pass the LH TC to Var's (aka function calls)
-- We DO NOT want to put it in DataCons
addLHTCExprPasses :: HM.HashMap Name Id -> Expr -> LHStateM Expr
addLHTCExprPasses m = modifyAppTopE (addLHTCExprPasses' m)

addLHTCExprPasses' :: HM.HashMap Name Id -> Expr -> LHStateM Expr
addLHTCExprPasses' m a@(App _ _)
    | (Data _:_) <- as = return a
    | otherwise = do    
        if any (isLHDict) as
            then return a
            else do
                a' <- addLHTCExprPasses'' m [] as
                return $ mkApp a'
    where
        as = unApp a

        isLHDict (Var (Id _ t))
            | TyCon (Name "lh" _ _ _) _ <- tyAppCenter t = True
        isLHDict _ = False

addLHTCExprPasses' _ e = return e

addLHTCExprPasses'' :: HM.HashMap Name Id -> [Expr] -> [Expr] -> LHStateM [Expr]
addLHTCExprPasses'' _ es [] = return $ reverse es
addLHTCExprPasses'' m es (te@(Type t):es') = do
    dict <- lhTCDict m t
    as <- addLHTCExprPasses'' m (dict:es) es'
    return $ te:as
addLHTCExprPasses'' m es (e:es')
    | Var (Id n _) <- e
    , Just dict <- HM.lookup n m = do
        as <- addLHTCExprPasses'' m (Var dict:es) es'
        return $ e:as
    | otherwise = do
        as <- addLHTCExprPasses'' m [] es'
        return $ reverse es ++ e:as

-- We want to add a LH Dict Type argument to Var's and Cases, but not DataCons or Lambdas.
-- That is: function calls need to be passed the LH Dict but it
-- doesn't need to be passed around in DataCons
addLHDictToTypes :: ASTContainerM e Expr => HM.HashMap Name Id -> e -> LHStateM e
addLHDictToTypes m = modifyASTsM (addLHDictToTypes' m)

addLHDictToTypes' :: HM.HashMap Name Id -> Expr -> LHStateM Expr
addLHDictToTypes' m (Var (Id n t)) = return . Var . Id n =<< addLHDictToTypes'' m t
addLHDictToTypes' m (Case e i t a) = do
    t' <- addLHDictToTypes'' m t
    return $ Case e i t' a
addLHDictToTypes' _ e = return e

addLHDictToTypes'' :: HM.HashMap Name Id -> Type -> LHStateM Type
addLHDictToTypes'' m t@(TyForAll (NamedTyBndr _) _) = addLHDictToTypes''' m [] t
addLHDictToTypes'' m t = modifyChildrenM (addLHDictToTypes'' m) t

addLHDictToTypes''' :: HM.HashMap Name Id -> [Id] -> Type -> LHStateM Type
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

lhTCDict :: HM.HashMap Name Id -> Type -> LHStateM Expr
lhTCDict m t = do
    lh <- lhTCM
    tc <- typeClassInstTC m lh t
    case tc of
        Just e -> return $ dropAppedLH e
        Nothing -> return $ Var (Id (Name "bad2" Nothing 0 Nothing) (TyCon lh TYPE))
    where
        -- typeClassInstTC adds any needed LH Dict arguments for us.
        -- Unfortunately, the LH Dicts are then added AGAIN, by addLHTCExprEnvPasses
        -- So we just drop the LH Dicts added by typeClassInstTC, and everything works out
        dropAppedLH :: Expr -> Expr
        dropAppedLH (App e t'@(Type _)) = App (dropAppedLH e) t'
        dropAppedLH (App e _) = dropAppedLH e
        dropAppedLH e = e
