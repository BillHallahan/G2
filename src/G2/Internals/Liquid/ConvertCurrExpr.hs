{-# LANGUAGE LambdaCase#-}

module G2.Internals.Liquid.ConvertCurrExpr (convertCurrExpr) where

import G2.Internals.Language
import qualified G2.Internals.Language.ExprEnv as E
import G2.Internals.Language.Monad

import G2.Internals.Liquid.Conversion
import G2.Internals.Liquid.Types
import qualified Data.Map as M
import Data.Maybe

import Debug.Trace

convertCurrExpr :: Id -> LHStateM Id
convertCurrExpr ifi = do
    ifi' <- modifyInputExpr ifi
    addCurrExprAssumption ifi
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
modifyInputExpr :: Id -> LHStateM Id
modifyInputExpr i@(Id n _) = do
    (CurrExpr er ce) <- currExpr

    e <- lookupE n
    case e of
        Just je -> do
            newI <- modifyInputExpr' i je

            let ce' = replaceASTs (Var i) (Var newI) ce

            putCurrExpr (CurrExpr er ce')
            return newI
        Nothing -> error "Nothing" -- return ()

-- Actually does the work of modify the function for modifyInputExpr
-- Inserts the new function in the ExprEnv, and returns the Id
modifyInputExpr' :: Id -> Expr -> LHStateM Id
modifyInputExpr' i e = do
    e' <- letLiftFuncs =<< rebindFuncs e

    newI <- freshSeededIdN (idName i) (typeOf i)
    insertE (idName newI) e'

    return newI

rebindFuncs :: Expr -> LHStateM Expr
rebindFuncs e = return e

-- We want to get all function calls into Let Bindings.
-- This is a bit tricky- we can't just get all calls at once,
-- stick them in a let binding, and then rewrite, because the calls may be nested.
-- So we gather them up, one by one, and rewrite as we go.
-- Furthermore, we have to be careful to not move bindings from Lambdas/other Let's
-- out of scope.
letLiftFuncs :: Expr -> LHStateM Expr
letLiftFuncs = modifyAppTopE letLiftFuncs'

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
addCurrExprAssumption :: Id -> LHStateM ()
addCurrExprAssumption ifi = do
    (CurrExpr er ce) <- currExpr

    assumpt <- lookupAssumptionM (idName ifi)
    fi <- fixedInputs
    is <- inputIds

    lh <- mapM (lhTCDict'' M.empty) $ mapMaybe typeType fi

    let (typs, ars) = span isType $ fi ++ map Var is

    case assumpt of
        Just assumpt' -> do
            let appAssumpt = mkApp $ assumpt':typs ++ lh ++ ars
            let ce' = Assume appAssumpt ce
            putCurrExpr (CurrExpr er ce')
        Nothing -> return ()

isType :: Expr -> Bool
isType (Type _) = True
isType _ = False

typeType :: Expr -> Maybe Type
typeType (Type t) = Just t
typeType _ = Nothing