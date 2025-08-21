{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module G2.Liquid.ConvertCurrExpr ( convertCurrExpr
                                 , initiallyCalledFuncName) where

import G2.Language
import G2.Language.Monad
import qualified G2.Language.ExprEnv as E

import G2.Liquid.Conversion
import G2.Liquid.Types

import Control.Monad.Extra
import qualified Data.HashMap.Lazy as HM
import Data.Maybe

-- | Returns (1) the Id of the new main function and (2) the functions that need counterfactual variants
convertCurrExpr :: TV.TyVarEnv -> Id -> Bindings -> LHStateM (Id, [Name])
convertCurrExpr tv ifi bindings = do
    ifi' <- modifyInputExpr tv ifi
    mapWithKeyME (\(Name _ m _ _) e -> if isJust m then letLiftHigherOrder tv e else return e)
    addCurrExprAssumption tv ifi bindings
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
modifyInputExpr :: TV.TyVarEnv -> Id -> LHStateM (Id, [Name])
modifyInputExpr tv i@(Id n _) = do
    (CurrExpr er ce) <- currExpr

    e <- lookupE n
    case e of
        Just je -> do
            (newI, ns) <- modifyInputExpr' tv i je

            let ce' = replaceVarWithName (idName i) (Var newI) ce

            putCurrExpr (CurrExpr er ce')
            return (newI, ns)
        Nothing -> return (error "Name not found", [])

-- Actually does the work of modify the function for modifyInputExpr
-- Inserts the new function in the ExprEnv, and returns the Id
modifyInputExpr' :: TV.TyVarEnv -> Id -> Expr -> LHStateM (Id, [Name])
modifyInputExpr' tv i e = do
    (e', ns) <- rebindFuncs e
    e'' <- letLiftFuncs tv e'
    e''' <- replaceLocalAssert i e''

    newI <- freshSeededIdN (idName i) (typeOf tv i)
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

-- | We are assuming the precondiiton holds, so we only have to check the postcondition!
-- We also replace the name of the assert so we can recognize it as the inital call later.
replaceLocalAssert :: Id -> Expr -> LHStateM Expr
replaceLocalAssert (Id n _) ce = do
    n_assert <- lookupPostM n
    -- Replace the initial function assertion with one that only checks the postcondition,
    -- but is careful to not replace assertions tied to higher order functions.
    let ce' = insertInLams
                (\_ e -> case e of
                            Let b (Assert (Just fc) e1 e2) ->
                                let ars = arguments fc ++ [returns fc]
                                    assrt = case n_assert of
                                                Just a -> mkApp (a:ars)
                                                Nothing -> e1
                                in 
                                Let b $ Assert (Just fc) assrt e2
                            _ -> e) ce
        ce'' = modifyASTs
                (\e -> case e of
                        Assert (Just fc) e1 e2 ->
                            Assert (Just $ fc { funcName = initiallyCalledFuncName}) e1 e2
                        _ -> e) ce'
    return ce''

initiallyCalledFuncName :: Name
initiallyCalledFuncName = Name "INITIALLY_CALLED_FUNC" Nothing 0 Nothing

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
letLiftFuncs :: TV.TyVarEnv -> Expr -> LHStateM Expr
letLiftFuncs tv e = do
    e' <- modifyAppTopE (letLiftFuncs' tv) e
    return $ flattenLets e'

letLiftFuncs' :: TV.TyVarEnv -> Expr -> LHStateM Expr
letLiftFuncs' tv e
    | ars <- passedArgs e
    , any (\case { Var _ -> False; Type _ -> False; _ -> True }) ars = do
        let c = appCenter e
        (binds, f_ars) <- liftSel tv ars
        return . Let binds . mkApp $ c:f_ars
        -- let c = appCenter e
        -- is <- freshIdsN $ map (typeOf tv) ars

        -- return . Let (zip is ars) . mkApp $ c:map Var is
    | otherwise = return e

liftSel :: TV.TyVarEnv -> [Expr] -> LHStateM ([(Id, Expr)], [Expr])
liftSel tv = go ([], [])
    where
        go (binds, r_es) [] = return (binds, reverse r_es)
        go (binds, r_es) (e:es) =
            case e of
                Var _ -> go (binds, e:r_es) es
                Type _ -> go (binds, e:r_es) es
                _ -> do
                    i <- freshIdN $ typeOf tv e
                    go ((i, e):binds, Var i:r_es) es

-- | Tries to be more selective then liftLetFuncs, doesn't really work yet...
letLiftHigherOrder :: TV.TyVarEnv -> Expr -> LHStateM Expr
letLiftHigherOrder tv e = return . shiftLetsOutOfApps =<< insertInLamsE (letLiftHigherOrder' tv) e

letLiftHigherOrder' :: TV.TyVarEnv -> [Id] -> Expr -> LHStateM Expr
letLiftHigherOrder' tv is e@(App _ _)
    | Var i <- appCenter e
    , i `elem` is = do
        ni <- freshIdN (typeOf tv e)
        e' <- modifyAppRHSE (letLiftHigherOrder' tv is) e
        return $ Let [(ni, e')] (Var ni)
    | d@(Data _) <- appCenter e = do
        let ars = passedArgs e
        f_is <- freshIdsN $ map (typeOf tv) ars

        ars' <- mapM (letLiftHigherOrder' tv f_is) ars

        return . Let (zip f_is ars') . mkApp $ d:map Var f_is
letLiftHigherOrder' tv is e@(Lam _ _ _) = insertInLamsE (\is' -> letLiftHigherOrder' tv (is ++ is')) e
letLiftHigherOrder' tv is e = modifyChildrenM (letLiftHigherOrder' tv is) e

shiftLetsOutOfApps :: Expr -> Expr
shiftLetsOutOfApps e@(App _ _) =
    case shiftLetsOutOfApps' e of
        Let b e' -> Let b . modifyBottomApp shiftLetsOutOfApps $ e'
        e' -> modifyBottomApp shiftLetsOutOfApps $ e'
shiftLetsOutOfApps e = modifyChildren shiftLetsOutOfApps e

shiftLetsOutOfApps' :: Expr -> Expr
shiftLetsOutOfApps' a@(App _ _) =
    let
        b = getLetsInApp a
    in
    case b of
        [] -> a
        _ -> Let b $ elimLetsInApp a
shiftLetsOutOfApps' _ = error "shiftLetsOutOfApps': must be passed an App"

getLetsInApp :: Expr -> Binds
getLetsInApp (Let b e) = b ++ getLetsInApp e
getLetsInApp (App e e') = getLetsInApp e ++ getLetsInApp e'
getLetsInApp _ = []

elimLetsInApp :: Expr -> Expr
elimLetsInApp (Let _ e) = elimLetsInApp e
elimLetsInApp (App e e') = App (elimLetsInApp e) (elimLetsInApp e')
elimLetsInApp e = e

modifyBottomApp :: (Expr -> Expr) -> Expr -> Expr
modifyBottomApp f (App e e') = App (modifyBottomApp f e) (modifyBottomApp f e')
modifyBottomApp f e = f e

-- We add an assumption about the inputs to the current expression
-- This prevents us from finding a violation of the output refinement type
-- that requires a violation of the input refinement type
addCurrExprAssumption :: TV.TyVarEnv -> Id -> Bindings -> LHStateM ()
addCurrExprAssumption tv ifi (Bindings {fixed_inputs = fi}) = do
    (CurrExpr er ce) <- currExpr

    lh_tc_n <- lhTCM
    let lh_tc = TyCon lh_tc_n (TyFun TYPE TYPE)
    let fi' = filter (\e -> tyAppCenter (typeOf tv e) /= lh_tc) fi

    assumpt <- lookupAssumptionM (idName ifi)
    -- fi <- fixedInputs
    eenv <- exprEnv
    inames <- inputNames
    let inames' = take (length $ argumentTypes $ typeOf tv ifi) inames

    lh <- mapM (lhTCDict' HM.empty) $ mapMaybe typeType fi'

    let is = catMaybes (map (E.getIdFromName eenv) inames')   
    let (typs, ars) = span isType $ fi' ++ map Var is

    case assumpt of
        Just (assumpt_is, higher_is, assumpt') -> do
            let all_args = typs ++ lh ++ ars
                appAssumpt = mkApp $ assumpt':all_args

            inputs <- inputNames
            let matching = zipWith (\n (i, hi) -> (n, i, hi)) inputs $ drop (length higher_is - length inputs) $ zip assumpt_is higher_is
                matching_higher = mapMaybe (\(n, i, hi) -> maybe Nothing (Just . (n, i,)) hi) matching
                let_expr = Let (map (\(n, i, _) -> (snd i, Var (Id n . typeOf tv $ snd i))) matching_higher)

            let ce' = let_expr
                    . flip (foldr (uncurry replaceAssumeFC)) (map (\(n, (_, i), _) -> (idName i, n)) matching_higher)
                    $ foldr (uncurry replaceVar) ce (map (\(n, _, hi) -> (n, hi)) matching_higher)
                assume_ce = Assume Nothing appAssumpt ce'

            putCurrExpr (CurrExpr er assume_ce)
        Nothing -> return ()

replaceAssumeFC :: ASTContainer m Expr => Name -> Name -> m -> m
replaceAssumeFC old new = modifyASTs (replaceAssumeFC' old new)

replaceAssumeFC' :: Name -> Name -> Expr -> Expr
replaceAssumeFC' old new e@(Assume (Just fc) e1 e2) =
    if funcName fc == old then Assume (Just (fc { funcName = new })) e1 e2 else e
replaceAssumeFC' _ _ e = e

isType :: Expr -> Bool
isType (Type _) = True
isType _ = False

typeType :: Expr -> Maybe Type
typeType (Type t) = Just t
typeType _ = Nothing
