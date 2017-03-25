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
        applyDataConAdj applies .
        modifyTypesInExpr (applyTypeAdj applies) .
        modify (applyFuncGen applies) $ s
    where
        --adjusts calls to functions to accept apply datatypes rather than
        --functions
        applyFuncGen :: AppliesLookUp -> Expr -> Expr
        applyFuncGen a app@(App (Var n t) e) =
            let
                r = lookup t a
            in
            case r of
                Just (f, d) ->
                    let
                        applyVar = (Var f (TyFun (TyConApp d []) t))
                        applyType = Var n (TyConApp d [])
                    in 
                    App (App applyVar applyType) e
                Nothing -> app
        applyFuncGen _ e = e

        --adjusts the types of expressions to account for apply
        applyTypeAdj :: AppliesLookUp -> Expr -> Type -> Type
        applyTypeAdj a e t@(TyFun t'@(TyFun _ _) t'') =
            let
                r = lookup t' a    
            in
            case r of Just (f, d) -> TyFun (TyConApp d []) t'' 
                      Nothing -> t
        applyTypeAdj _ _ t = t

        applyDataConAdj :: (Manipulatable Expr m, Manipulatable Type m) => AppliesLookUp -> m -> m
        applyDataConAdj a e = modifyDataConExpr (applyDataConAdj' a) e
            where
                applyDataConAdj' :: AppliesLookUp -> DataCon -> DataCon
                applyDataConAdj' a (DC (n, i, t, ts)) =
                    let ts' = map (\t' -> case lookup t' $ a of
                                                Just (_, t'') -> TyConApp t'' []
                                                Nothing -> t'
                                  ) ts in
                    DC (n, i, t, ts')

        --adjust passed functions, and calls to passed functions, to use apply variables rather than higher order functions
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
                                (Just (f', d), Just d') ->
                                    applyPassedFuncsSnd (Var f t) (Var d' (TyAlg d [])) .
                                    applyPassedFuncsFst (Var f t) (App (applyFunc f' d t) (Var d' (TyAlg d []))) $ s
                                _ -> s
                    in
                    applyPassedFuncs' a a' fs s'

                applyPassedFuncs'' :: Expr -> Expr -> Expr -> Expr
                applyPassedFuncs'' r r' e = applyPassedFuncsSnd r r' . applyPassedFuncsFst r r' $ e

                --A passed function may appear in either position in App
                --If it appears in the first position, it is being called
                --If it appears in the second position, it is being passed
                --We have a seperate function for each case.
                applyPassedFuncsFst :: (Manipulatable Expr s) => Expr -> Expr -> s -> s
                applyPassedFuncsFst r r' e = modify (applyPassedFuncsFst' r r') e
                    where
                        applyPassedFuncsFst' :: Expr -> Expr -> Expr -> Expr
                        applyPassedFuncsFst' r r' a@(App e e') = if e == r then App r' e' else a
                        applyPassedFuncsFst' _ _ e = e

                applyPassedFuncsSnd :: (Manipulatable Expr s) => Expr -> Expr -> s -> s
                applyPassedFuncsSnd r r' e = modify (applyPassedFuncsSnd' r r') e
                    where
                        applyPassedFuncsSnd' :: Expr -> Expr -> Expr -> Expr
                        applyPassedFuncsSnd' r r' a@(App e e') = if e' == r then App e r' else a
                        applyPassedFuncsSnd' _ _ e = e
                    
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

                e' = Case (Var frApply . TyConApp d $ []) cases t2

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

--This returns a mapping from all higher order function types to
--names for cooresponding Apply functions and data types
higherOrderFuncTypesToApplies :: (Manipulatable Expr m, Manipulatable Type m) => m -> AppliesLookUp
higherOrderFuncTypesToApplies e =
    let
        h = findPassedInFuncTypes e
        bv = freeVars [] e
        funcN = numFresh "apply" (length h) bv
        funcD = numFresh "applyType" (length h) (bv ++ funcN)
    in 
    zip h . zip funcN $ funcD

--gets all functions passed in as higher order functions and stores new there types,
--the name of the function, and a new name for a cooresponding data constructor
passedInFuncsToApplies :: State -> AppliesConLookUp
passedInFuncsToApplies s = 
    let
        passed = findPassedInFuncs s
        types = findPassedInFuncTypes s

        lam_vars = eval getLamCaseVars s

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

        getLamCaseVars :: Expr -> [(FuncName, Type)]
        getLamCaseVars (Lam n _ t) = [(n, t)]
        getLamCaseVars (Case a ae t) = concatMap findPassedInFuncsAE ae
        getLamCaseVars _ = []

-- Get the type of all higher order function arguments
findPassedInFuncTypes :: Manipulatable Type m => m -> [Type]
findPassedInFuncTypes e = nub . eval findPassedInFuncTypes' $ e
    where
        findPassedInFuncTypes' :: Type -> [Type]
        findPassedInFuncTypes' (TyAlg _ dc) = concatMap findPassedInFuncTypesDC dc
        findPassedInFuncTypes' (TyFun t@(TyFun _ _) _) = [t]
        findPassedInFuncTypes' _ = []

        findPassedInFuncTypesDC :: DataCon -> [Type]
        findPassedInFuncTypesDC (DC (_, _, _, t)) = filter isTyFun t

--Returns all functions (either free, from lambdas, or from pattern matching) being passed into another function
findPassedInFuncs :: Manipulatable Expr m => m -> [(FuncName, Type)]
findPassedInFuncs s = nub . eval findPassedInFuncs' $ s
    where
        findPassedInFuncs' :: Expr -> [(FuncName, Type)]
        findPassedInFuncs' (App _ (Var n t@(TyFun _ _))) = [(n, t)]
        findPassedInFuncs' (Case e ae t) = concatMap findPassedInFuncsAE ae
        findPassedInFuncs' _ = []

findPassedInFuncsAE :: (Alt, Expr) -> [(FuncName, Type)]
findPassedInFuncsAE (Alt (DC (_, _, _, t), n), _) = filter (isTyFun . snd) . zip n $ t

--returns all expressions corresponding to higher order functions in the given expr
findHigherOrderFuncs :: (Manipulatable Expr m) => m -> [Expr]
findHigherOrderFuncs e = nub . evalTypesInExpr (findHigherOrderFuncs') e $ []
    where
        findHigherOrderFuncs' :: Expr -> Type -> [Expr]
        findHigherOrderFuncs' e' t = if isHigherOrderFuncType t then [e'] else []

--returns whether the given type is a higher order func type, for example (a -> b) -> a -> b
isHigherOrderFuncType :: Type -> Bool
isHigherOrderFuncType t = Mon.getAny . eval (Mon.Any . isHigherOrderFuncType') $ t
    where
        isHigherOrderFuncType' :: Type -> Bool
        isHigherOrderFuncType' (TyFun (TyFun _ _) _) = True
        isHigherOrderFuncType' (TyFun (TyConApp _ t) _) = any isTyFun t
        isHigherOrderFuncType' _ = False
    
isTyFun :: Type -> Bool
isTyFun (TyFun _ _) = True
isTyFun _ = False