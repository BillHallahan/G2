{-# Language FlexibleContexts #-}

module G2.Internals.Liquid.Simplify ( simplify ) where

import G2.Internals.Language
import G2.Internals.Language.Monad
import G2.Internals.Liquid.Types

-- The LH translation generates certain redundant Expr's over and over again.
-- Here we stamp them out.
simplify :: LHStateM ()
simplify = do
    simplifyExprEnv
    mapCurrExpr simplifyExpr
    mapAnnotsExpr simplifyExpr

simplifyExprEnv :: LHStateM ()
simplifyExprEnv = mapME simplifyExpr

simplifyExpr :: Expr -> LHStateM Expr
simplifyExpr = fixM simplifyExpr'

simplifyExpr' :: Expr -> LHStateM Expr
simplifyExpr' e = simplifyTrueLams =<< simplifyAnds =<< simplifyLHPP e

-- simplifyTrueLams
simplifyTrueLams :: Expr -> LHStateM Expr
simplifyTrueLams e = do
    true <- mkTrueE
    modifyASTsM (simplifyTrueLams' true) e

simplifyTrueLams' :: Expr -> Expr -> LHStateM Expr
simplifyTrueLams' true e@(App (Lam _ _ le) _) = 
    if true == le then return true else return e
simplifyTrueLams' _ e = return e

-- simplifyLHPP
simplifyLHPP :: Expr -> LHStateM Expr
simplifyLHPP e = do
    true <- mkTrueE
    modifyAppTopE (simplifyLHPP' true) e

simplifyLHPP' :: Expr -> Expr -> LHStateM Expr
simplifyLHPP' true e = do
    lhpp <- lhPPM

    let a = unApp e

    case a of
        ((Var (Id n _)):as) -> 
            if n == lhpp && all (redundantLHPPArg true) as
                then return true
                else return e
        _ -> return e

-- Checks if an argument to a LHPP call makes that call nonredundant
-- A LHPP call is redundant if all function arguments are just (\_ -> True)
redundantLHPPArg :: Expr -> Expr -> Bool
redundantLHPPArg true (Lam _ _ e) = true == e
redundantLHPPArg _ _ = True

-- simplifyAnds
simplifyAnds :: Expr -> LHStateM Expr
simplifyAnds e = do
    andE <- lhAndE
    true <- mkTrueE
    modifyAppTopE (simplifyAnds' andE true) e

simplifyAnds' :: Expr -> Expr -> Expr -> LHStateM Expr
simplifyAnds' andE true e = do
    let a = unApp e

    case a of
        [e1, e2, e3]
            | e1 == andE
            , e2 == true -> return e3
            | e1 == andE
            , e3 == true -> return e2
            | otherwise -> return e
        _ -> return e

-- helpers
fixM :: (Monad m, Eq a) => (a -> m a) -> a -> m a
fixM f e = do
    e' <- f e
    if e == e' then return e else fixM f e'