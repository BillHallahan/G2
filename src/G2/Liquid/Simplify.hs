{-# Language FlexibleContexts #-}
{-# Language OverloadedStrings #-}

module G2.Liquid.Simplify ( simplify
                          , furtherSimplifyCurrExpr ) where

import G2.Language
import G2.Language.CallGraph
import qualified G2.Language.ExprEnv as E
import qualified G2.Language.Simplification as GSimp
import G2.Language.Monad
import G2.Liquid.Types

import qualified Data.HashSet as HS
import qualified Data.Text as T

import Debug.Trace

-- | The LH translation generates certain redundant Expr's over and over again.
-- Here we stamp them out.
simplify :: LHStateM ()
simplify = do
    removeRedundantAsserts
    simplifyExprEnv
    mapCurrExpr simplifyExpr
    mapAssumptionsM simplifyExpr
    mapAnnotsExpr simplifyExpr

    in_eenv <- inlineEnv
    in_case_env <- inlineInCaseEnv
    mapAssumptionsM (return . GSimp.simplifyExprs in_eenv in_case_env)
    mapPostM (return . GSimp.simplifyExprs in_eenv in_case_env)
    mapE (GSimp.simplifyExprs in_eenv in_case_env)
    mapMeasuresM (return . GSimp.simplifyExprs in_eenv in_case_env)

furtherSimplifyCurrExpr :: LHStateM ()
furtherSimplifyCurrExpr = do
    in_eenv <- inlineEnv
    in_case_env <- inlineInCaseEnv
    mapCurrExpr (return . GSimp.simplifyExprs in_eenv in_case_env)

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


-- | Asserts in the default numerical classes just reflect the actual function definition directly,
-- so we can remove them to save some time.
removeRedundantAsserts :: LHStateM ()
removeRedundantAsserts = mapWithKeyME removeRedundantAsserts'

removeRedundantAsserts' :: Name -> Expr -> LHStateM Expr
removeRedundantAsserts' (Name n m _ _) e
    | (n, m) `HS.member` specFuncs = return $ elimAsserts e
    | otherwise = return e

-- | Environments for inlining
inlineEnv :: LHStateM ExprEnv
inlineEnv = do
    cg <- return . getCallGraph =<< exprEnv

    tcv <- tcValuesM
    lh_tc_n <- lhTCM
    lhnum_tc_n <- lhNumTCM

    g2_int <- tyIntT
    lh_int_tc <- measureClassDictExpr lh_tc_n g2_int
    num_int_tc <- regTCClassDictExpr lhnum_tc_n g2_int

    eenv <- exprEnv
    meas <- measuresM
    let lh_ns = names tcv ++ names lh_int_tc ++ names num_int_tc
        eenv' = E.filterWithKey (\n _ -> n `elem` lh_ns) $ E.union eenv meas
    return eenv'

inlineInCaseEnv :: LHStateM ExprEnv
inlineInCaseEnv = do
    tc <- typeClasses
    lh_tc_n <- lhTCM
    lh_num <- lhNumTCM
    let all_lh_tc = lookupTCDicts lh_tc_n tc
        all_num_tc = lookupTCDicts lh_num tc

    eenv <- exprEnv
    meas <- measuresM
    let lh_ns = names all_lh_tc ++ names all_num_tc
        eenv' = E.filterWithKey (\n _ -> n `elem` lh_ns) $ E.union eenv meas
    return eenv'

measureClassDictExpr :: Name -> Type -> LHStateM (Maybe Expr)
measureClassDictExpr = classDictExpr lookupMeasureM lookupTCDictTC

regTCClassDictExpr :: Name -> Type -> LHStateM (Maybe Expr)
regTCClassDictExpr = classDictExpr lookupE lookupTCDictTC

classDictExpr :: (Name -> LHStateM (Maybe Expr))
              -> (Name -> Type -> LHStateM (Maybe Id))
              -> Name
              -> Type
              -> LHStateM (Maybe Expr)
classDictExpr look_ex look_tc n t = do
    i <- look_tc n t
    case i of
        Just i' -> look_ex (idName i')
        Nothing -> return Nothing

specFuncs :: HS.HashSet (T.Text, Maybe T.Text)
specFuncs = HS.fromList [ ("+", Just "GHC.Num")
                        , ("-", Just "GHC.Num")
                        , ("*", Just "GHC.Num")
                        , ("negate", Just "GHC.Num")
                        , ("abs", Just "GHC.Num")
                        , ("signum", Just "GHC.Num")
                        , ("fromInteger", Just "GHC.Num")

                        , ("quot", Just "GHC.Real")
                        , ("rem", Just "GHC.Real")
                        , ("div", Just "GHC.Real")
                        , ("mod", Just "GHC.Real")
                        , ("quotRem", Just "GHC.Real")
                        , ("divMod", Just "GHC.Real")
                        , ("toInteger", Just "GHC.Real")

                        , ("==", Just "GHC.Classes")
                        , ("/=", Just "GHC.Classes")

                        , ("<", Just "GHC.Classes")
                        , ("<=", Just "GHC.Classes")
                        , (">", Just "GHC.Classes")
                        , (">=", Just "GHC.Classes")

                        , ("I#", Just "GHC.Types")
                        , ("True", Just "GHC.Types")
                        , ("False", Just "GHC.Types")]

