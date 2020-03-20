{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}

module G2.Liquid.ConvertCurrExpr (convertCurrExpr) where

import G2.Language
import G2.Language.Monad
import qualified G2.Language.ExprEnv as E

import G2.Liquid.Conversion
import G2.Liquid.Types

import Control.Monad.Extra
import qualified Data.Map as M
import Data.Maybe

import Debug.Trace

-- | Returns (1) the Id of the new main function and (2) the functions that need counterfactual variants
convertCurrExpr :: Id -> Bindings -> LHStateM (Id, [Name])
convertCurrExpr ifi bindings = do
    ifi' <- modifyInputExpr ifi
    addCurrExprAssumption ifi bindings
    return ifi'

-- We create a copy of the input function which is modified to:
--  (1) Call a different copy of each of it's internal functions.
--      This allows us to only nondeterministically branch into abstract
--      counterexamples from the initial function call
--      
--  (2) Call all functions in let bindings.  I.e., the following:
--          Just (f x)
--      would be changed to:
--      let fx = f x in Just fx
--      This way, if we reference the output in both the refinement and the body,
--      it'll only be computed once.  This is NOT just for efficiency.
--      Since the choice is nondeterministic, this is the only way to ensure that
--      we don't make two different choices, and get two different values.
modifyInputExpr :: Id -> LHStateM (Id, [Name])
modifyInputExpr i@(Id n _) = do
    (CurrExpr er ce) <- currExpr

    e <- lookupE n
    case e of
        Just je -> do
            (newI, ns) <- modifyInputExpr' i je

            let ce' = replaceVarWithName (idName i) (Var newI) ce

            putCurrExpr (CurrExpr er ce')
            return (newI, ns)
        Nothing -> return (error "Name not found", [])

-- Actually does the work of modify the function for modifyInputExpr
-- Inserts the new function in the ExprEnv, and returns the Id
modifyInputExpr' :: Id -> Expr -> LHStateM (Id, [Name])
modifyInputExpr' i e = do
    (e', ns) <- rebindFuncs e
    e''' <- letLiftFuncs e'

    newI <- freshSeededIdN (idName i) (typeOf i)
    insertE (idName newI) e'''

    return (newI, ns)

rebindFuncs :: Expr -> LHStateM (Expr, [Name])
rebindFuncs e = do
    vs <- mapMaybeM (\i -> fmap (i,) <$> lookupE (idName i)) $ varIds e
    nvs <- mapM (\(Id n t, _) -> freshSeededIdN n t) vs
    
    mapM_ (\(n, e_) -> insertE n (rewriteAssertName n e_)) $ zip (map idName nvs) (map snd vs)

    let e' = foldr (uncurry replaceASTs) e $ zip (map (Var . fst) vs) (map Var nvs)

    return (e', map idName nvs)
    where
        rewriteAssertName :: Name -> Expr -> Expr
        rewriteAssertName n (Assert (Just fc) e1 e2) = Assert (Just $ fc {funcName = n}) e1 e2
        rewriteAssertName n e1 = modifyChildren (rewriteAssertName n) e1

replaceVarWithName :: Name -> Expr -> Expr -> Expr
replaceVarWithName n new = modify (replaceVarWithName' n new)

replaceVarWithName' :: Name -> Expr -> Expr -> Expr
replaceVarWithName' n new v@(Var (Id n' _)) = if n == n' then new else v
replaceVarWithName' _ _ e = e

-- We want to get all function calls into Let Bindings.
-- This is a bit tricky- we can't just get all calls at once,
-- stick them in a let binding, and then rewrite, because the calls may be nested.
-- So we gather them up, one by one, and rewrite as we go.
-- Furthermore, we have to be careful to not move bindings from Lambdas/other Let's
-- out of scope.
letLiftFuncs :: Expr -> LHStateM Expr
letLiftFuncs e = do
    e' <- modifyAppTopE letLiftFuncs' e
    return $ e'

letLiftFuncs' :: Expr -> LHStateM Expr
letLiftFuncs' e
    | ars <- passedArgs e
    , any (\case { Var _ -> False; _ -> True }) ars = do
        let c = appCenter e
        is <- freshIdsN $ map typeOf ars

        return . Let (zip is ars) . mkApp $ c:map Var is
    | otherwise = return e

-- We add an assumption about the inputs to the current expression
-- This prevents us from finding a violation of the output refinement type
-- that requires a violation of the input refinement type
addCurrExprAssumption :: Id -> Bindings -> LHStateM ()
addCurrExprAssumption ifi (Bindings {fixed_inputs = fi}) = do
    (CurrExpr er ce) <- currExpr

    lh_tc_n <- lhTCM
    let lh_tc = TyCon lh_tc_n TYPE
    let fi' = filter (\e -> tyAppCenter (typeOf e) /= lh_tc) fi

    assumpt <- lookupAssumptionM (idName ifi)
    -- fi <- fixedInputs
    eenv <- exprEnv
    inames <- inputNames

    lh <- mapM (lhTCDict' M.empty) $ mapMaybe typeType fi'

    let is = catMaybes (map (E.getIdFromName eenv) inames)   
    let (typs, ars) = span isType $ fi' ++ map Var is

    case assumpt of
        Just assumpt' -> do
            let appAssumpt = mkApp $ assumpt':typs ++ lh ++ ars
            let ce' = Assume Nothing appAssumpt ce
            putCurrExpr (CurrExpr er ce')
        Nothing -> return ()

isType :: Expr -> Bool
isType (Type _) = True
isType _ = False

typeType :: Expr -> Maybe Type
typeType (Type t) = Just t
typeType _ = Nothing
