{-# LANGUAGE FlexibleContexts #-}

module G2.Core.Defunctionalizor where

import G2.Core.CoreManipulator
import G2.Core.Language
import G2.Core.Utils

import qualified Data.List as L
import qualified Data.Map  as M

import qualified Data.Monoid as Mon

import qualified Debug.Trace as T

{-Defunctionalizor

We need to eliminate higher order functions to
enable a translation to SMT formulas.

This can be done via Defunctionalization, described by Reynolds in
http://cs.au.dk/~hosc/local/HOSC-11-4-pp363-397.pdf

In short, each call to a higher order functions (a -> b) -> c is identified.
For each a, b pair, a new datatype A_B, and fresh function, apply_a_b :: A_B -> a -> b, is created.
-}

type FuncName = Name
type DataTypeName = Name
type DataConName = Name
type AppliesLookUp = [(Type, (FuncName, DataTypeName))]
type AppliesConLookUp = [(FuncName, DataConName)]


defunctionalize :: State -> State
defunctionalize s@(tv, ev, expr, pc) =
    let
        applies = higherOrderFuncTypesToApplies s
        appliesCons = passedInFuncsToApplies s
    in
    applyPassedFuncs applies appliesCons . modifyTypesInExpr (applyLamTypeAdj applies) . modifyUntil (applyFuncGen applies) $ s
    where
        isAppliesVar :: AppliesLookUp -> Expr -> Bool
        isAppliesVar a e =
            let
                t = typeOf e
                appNames = map (\(_, (_, d)) -> d) a
            in
            case t of TyConApp n [] -> n `elem` appNames
                      _ -> False

        --adjusts calls to functions to accept apply datatypes rather than
        --functions
        applyFuncGen :: AppliesLookUp -> Expr -> (Expr, Bool)
        applyFuncGen a e@(App (Var n t) app) =
            let
                r = lookup t a
            in
            case r of Just (f, d) ->
                                    let
                                        applyVar = Var f (TyFun (TyConApp d []) t)
                                        applyType = Var n (TyConApp d [])
                                    in 
                                    (App (App applyVar applyType) app, False)
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
            T.trace ("passed = " ++ show passed) applyPassedFuncs' a a' passed s
            where
                applyPassedFuncs' :: AppliesLookUp -> AppliesConLookUp -> [(FuncName, Type)] -> State -> State
                applyPassedFuncs' _ _ [] s = s
                applyPassedFuncs' a a' ((f, t):fs) s =
                    let
                        r = lookup t a
                        r' = lookup f a'
                        s' = case (r, r') of
                                (Just (f', d), Just d') -> replaceM s (Var f t) (App (applyFunc f' d t) (Var d' (TyAlg d [])))
                                otherwise -> s
                    in
                    applyPassedFuncs' a a' fs s'
                    
        --creates the actual apply function
        -- createApplyFuncs :: AppliesLookUp -> AppliesConsLookUp -> State -> State
        -- createApplyFuncs _ _ s = s
        -- createApplyFuncs ((t, (f, d)):as) a s =
        --     let
        --         --Get fresh variable for lambda
        --         bv = freeVars [] s
        --         fr = fresh "a" bv

        --         apply = Lam fr e' t
        --     in



        applyFunc :: Name -> Name -> Type -> Expr
        applyFunc f d t = Var f (TyFun (TyConApp d []) t) 


--Returns all Vars with the given Name
findFuncVar :: (Manipulatable Expr m) => Name -> m -> [Expr]
findFuncVar n e = eval (findFuncVar' n) e
    where
        findFuncVar' :: Name -> Expr -> [Expr]
        findFuncVar' n v@(Var n' t) = if n == n' then [v] else []
        findFuncVar _ _ = []

--Returns all functions (either free or from lambdas) being passed into another function
findPassedInFuncs :: State -> [(FuncName, Type)]
findPassedInFuncs s = eval (findPassedInFuncs') s
    where
        findPassedInFuncs' :: Expr -> [(FuncName, Type)]
        findPassedInFuncs' (App _ (Var n t@(TyFun _ _))) = [(n, t)]
        findPassedInFuncs' _ = []

-- Get the type of all higher order function arguments
findPassedInFuncTypes :: (Manipulatable Expr m) => m -> [Type]
findPassedInFuncTypes e = L.nub . eval findPassedInFuncTypes' . map typeOf . findHigherOrderFuncs $ e
    where
        findPassedInFuncTypes' :: Type -> [Type]
        findPassedInFuncTypes' (TyFun t@(TyFun _ _) _) = [t]
        findPassedInFuncTypes' _ = []

passedInFuncsToApplies :: State -> AppliesConLookUp
passedInFuncsToApplies s =
    let
        passed = map fst . findPassedInFuncs $ s
        bv = freeVars [] s
        fr = numFresh "applyCon" (length passed) bv
    in
    zip passed fr

--This returns a mapping from all higher order function types to
--names for cooresponding Apply functions and data types
higherOrderFuncTypesToApplies :: (Manipulatable Expr m) => m -> AppliesLookUp
higherOrderFuncTypesToApplies e =
    let
        h = findPassedInFuncTypes $ e
        bv = freeVars [] e
        funcN = numFresh "apply" (length h) bv
        funcD = numFresh "apply" (length h) (bv ++ funcN)
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
findHigherOrderFuncs e = L.nub . evalTypesInExpr (\e' t -> if isHigherOrderFuncType t then [e'] else []) e $ []

isHigherOrderFuncType :: Type -> Bool
isHigherOrderFuncType (TyFun t1 t2) = Mon.getAny . eval (Mon.Any . isLeadingHigherOrderFuncType) $ (TyFun t1 t2)
isHigherOrderFuncType _ = False

isLeadingHigherOrderFuncType :: Type -> Bool
isLeadingHigherOrderFuncType (TyFun (TyFun _ _) _) = True
isLeadingHigherOrderFuncType (TyFun (TyConApp _ t) _) = foldr (||) False . map isTyFun $ t
    where
        isTyFun :: Type -> Bool
        isTyFun (TyFun _ _) = True
        isTyFun _ = False
isLeadingHigherOrderFuncType _ = False