{-# LANGUAGE FlexibleContexts #-}

module G2.Core.Defunctionalizor where

import G2.Core.CoreManipulator
import G2.Core.Language
import G2.Core.Utils

import Data.List
import qualified Data.Map  as M

import qualified Data.Monoid as Mon

import qualified Data.Semigroup as Semi

{-Defunctionalizor

We need to eliminate higher order functions to
enable a translation to SMT formulas.

This can be done via Defunctionalization, described by Reynolds in
http://cs.au.dk/~hosc/local/HOSC-11-4-pp363-397.pdf

In short, each call to a higher order functions (a -> b) -> c is identified.
For each a, b pair, a new datatype A_B, and fresh function,
apply_a_b :: A_B -> a -> b, is created.
-}

type FuncName = Name
type DataTypeName = Name
type DataConName = Name
type AppliesLookUp = [(Type, (FuncName, DataTypeName))]
type AppliesConLookUp = [(Type, [(FuncName, DataConName)])]


defunctionalize :: State -> State
defunctionalize s =
    let
        applies = higherOrderFuncTypesToApplies s
        appliesCons = passedInFuncsToApplies s
    in
    createApplyFuncs applies appliesCons .
        createApplyTypes applies appliesCons .
        applyPassedFuncs applies appliesCons .
        modifyTypesInExpr (applyLamTypeAdj applies) .
        modifyUntil (applyFuncGen applies) $ s
    where
        --adjusts calls to functions to accept apply datatypes rather than
        --functions
        applyFuncGen :: AppliesLookUp -> Expr -> (Expr, Bool)
        applyFuncGen a e@(Var n t) =
            let
                r = lookup t a
            in
            case r of
                Just (f, d) ->
                    let
                        applyVar = Var f (TyFun (TyConApp d []) t)
                        applyType = Var n (TyConApp d [])
                    in 
                    (App applyVar applyType, False)
                Nothing -> (e, True)
        applyFuncGen _ e = (e, True)

        --adjusts the types of lambda expressions to account for apply
        applyLamTypeAdj :: AppliesLookUp -> Expr -> Type -> Type
        applyLamTypeAdj a e t@(TyFun t'@(TyFun _ _) t'') =
            let
                r = lookup t' a    
            in
            case r of Just (f, d) -> TyFun (TyConApp d []) t'' 
                      Nothing -> t
        applyLamTypeAdj _ _ t = t

        --adjust lambda expressions and functions being passed to
        --use apply variables rather than higher order functions
        applyPassedFuncs :: AppliesLookUp -> AppliesConLookUp -> State -> State
        applyPassedFuncs a a' s =
            let
                passed = findPassedInFuncs s
            in
            applyPassedFuncs' a a' passed s
            where
                applyPassedFuncs' :: AppliesLookUp -> AppliesConLookUp -> [(FuncName, Type)] -> State -> State
                applyPassedFuncs' _ _ [] s = s
                applyPassedFuncs' a a' ((f, t):fs) s =
                    let
                        r = lookup t a
                        r' = lookup f . concatMap snd $ a'
                        s' = case (r, r') of
                                (Just (f', d), Just d') -> replaceM s (Var f t) (App (applyFunc f' d t) (Var d' (TyAlg d [])))
                                _ -> s
                    in
                    applyPassedFuncs' a a' fs s'
                    
        --adds the apply data types to the type environment
        createApplyTypes :: AppliesLookUp -> AppliesConLookUp -> State -> State
        createApplyTypes _ [] s = s
        createApplyTypes a ((t, fd):as) (t', env, ex, pc) =
            let
                name = snd (case lookup t a of
                            Just n -> n
                            Nothing -> error "Missing type in createApplyTypes in Defunctionalizor.hs")

                minTag = Semi.getMin . eval getMinTag $ t'

                cons = map (\((_, d), m) -> DC (d, m, TyConApp name [], [])) . zip fd $ [minTag - 1, minTag - 2..]
                d = TyAlg name cons
                t'' = M.insert name d t'
            in
            createApplyTypes a as (t'', env, ex, pc)
            where
                getMinTag :: Type -> Semi.Min Int
                getMinTag (TyAlg _ d) = 
                    if not . null $ d then
                        Semi.Min . minimum . map (\(DC (_, i, _, _)) -> i) $ d
                    else
                        mempty
                getMinTag _ = mempty

        --creates the actual apply function
        createApplyFuncs :: AppliesLookUp -> AppliesConLookUp -> State -> State
        createApplyFuncs ((t@(TyFun _ t2), (f, d)):as) a (t', env, ex, pc) =
            let
                --Get fresh variable for lambda
                bv = freeVars [] s
                frApply = fresh "a" bv

                frIn = fresh "i" (frApply:bv)

                c = case lookup t a of Just c' -> c'
                                       Nothing -> []

                cases = map (genCase (frApply:frIn:bv) frIn (TyConApp d []) t) c

                e' = Case (Var frApply . TyAlg d $ []) cases t2

                apply = Lam frApply (Lam frIn e' t) (TyFun (TyAlg d []) t)

                env' = M.insert f apply env
            in
            createApplyFuncs as a (t', env', ex, pc)
            where
                genCase :: [Name] -> Name -> Type -> Type -> (FuncName, DataConName) -> (Alt, Expr)
                genCase a i t t'@(TyFun t'' _) (f, d) = (Alt (DC (d, -1000, t, []), [fresh "new" a]), App (Var f t') (Var i t''))
                genCase _ _ _ _ _ = error "Second supplied type must be a function."
        createApplyFuncs _ _ s = s
        

        applyFunc :: Name -> Name -> Type -> Expr
        applyFunc f d t = Var f (TyFun (TyConApp d []) t)

--Returns all Vars with the given Name
findFuncVar :: (Manipulatable Expr m) => Name -> m -> [Expr]
findFuncVar n e = eval (findFuncVar' n) e
    where
        findFuncVar' :: Name -> Expr -> [Expr]
        findFuncVar' n v@(Var n' _) = if n == n' then [v] else []
        findFuncVar' _ _ = []

--Returns all functions (either free or from lambdas) being passed into another function
findPassedInFuncs :: Manipulatable Expr m => m -> [(FuncName, Type)]
findPassedInFuncs s = eval findPassedInFuncs' s
    where
        findPassedInFuncs' :: Expr -> [(FuncName, Type)]
        findPassedInFuncs' (App _ (Var n t@(TyFun _ _))) = [(n, t)]
        findPassedInFuncs' _ = []

-- Get the type of all higher order function arguments
findPassedInFuncTypes :: (Manipulatable Expr m) => m -> [Type]
findPassedInFuncTypes e = nub . eval findPassedInFuncTypes' . map typeOf . findHigherOrderFuncs $ e
    where
        findPassedInFuncTypes' :: Type -> [Type]
        findPassedInFuncTypes' (TyFun t@(TyFun _ _) _) = [t]
        findPassedInFuncTypes' _ = []
        
passedInFuncsToApplies :: State -> AppliesConLookUp
passedInFuncsToApplies s@(_, env, _, _) = 
    let
        passed = findPassedInFuncs env
        types = findPassedInFuncTypes s

        lam_vars = eval getLamVars s

        passed' = deleteFirstsBy (\n n' -> fst n == fst n') passed lam_vars

        bv = freeVars [] s
        fr = numFresh "applyCon" (length passed') bv
        passed_fr = zip passed' fr
    in
    passedIn' types passed_fr
    where
        passedIn' :: [Type] -> [((FuncName, Type), DataConName)] -> AppliesConLookUp
        passedIn' (t:ts) ftd =
            let
                rel = filter (\((_, t'), _) -> t == t') ftd
                fd = map (\((f, _), d) -> (f, d)) rel
            in
            (t, fd):passedIn' ts ftd
        passedIn' _ _ = []

        getLamVars :: Expr -> [(Name, Type)]
        getLamVars (Lam n _ t) = [(n, t)]
        getLamVars _ = []

--This returns a mapping from all higher order function types to
--names for cooresponding Apply functions and data types
higherOrderFuncTypesToApplies :: (Manipulatable Expr m) => m -> AppliesLookUp
higherOrderFuncTypesToApplies e =
    let
        h = findPassedInFuncTypes e
        bv = freeVars [] e
        funcN = numFresh "apply" (length h) bv
        funcD = numFresh "applyType" (length h) (bv ++ funcN)
    in 
    zip h . zip funcN $ funcD

--returns all expressions of the form (a -> b) -> c in the given expr
findLeadingHigherOrderFuncs :: (Manipulatable Expr m) => m -> [Expr]
findLeadingHigherOrderFuncs e = filter isLam . findLeadingHigherOrderFuncsAndCalls $ e
    where
        isLam :: Expr -> Bool
        isLam (Lam _ _ _) = True
        isLam _ = False

findLeadingHigherOrderFuncCalls :: (Manipulatable Expr m) => m -> [Expr]
findLeadingHigherOrderFuncCalls e = filter isVar . findLeadingHigherOrderFuncsAndCalls $ e
    where
        isVar :: Expr -> Bool
        isVar (Var _ _) = True
        isVar _ = False

--Returns both lambda functions and calling sites
findLeadingHigherOrderFuncsAndCalls :: (Manipulatable Expr m) => m -> [Expr]
findLeadingHigherOrderFuncsAndCalls e = filter (isLeadingHigherOrderFuncType . typeOf) (findHigherOrderFuncs e)

--returns all expressions corresponding to higher order functions in the given expr
findHigherOrderFuncs :: (Manipulatable Expr m) => m -> [Expr]
findHigherOrderFuncs e = nub . evalTypesInExpr (\e' t -> if isHigherOrderFuncType t then [e'] else []) e $ []

isHigherOrderFuncType :: Type -> Bool
isHigherOrderFuncType (TyFun t1 t2) = Mon.getAny . eval (Mon.Any . isLeadingHigherOrderFuncType) $ TyFun t1 t2
isHigherOrderFuncType _ = False

isLeadingHigherOrderFuncType :: Type -> Bool
isLeadingHigherOrderFuncType (TyFun (TyFun _ _) _) = True
isLeadingHigherOrderFuncType (TyFun (TyConApp _ t) _) = any isTyFun t
    where
        isTyFun :: Type -> Bool
        isTyFun (TyFun _ _) = True
        isTyFun _ = False
isLeadingHigherOrderFuncType _ = False