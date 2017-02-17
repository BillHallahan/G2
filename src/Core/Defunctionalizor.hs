{-# LANGUAGE FlexibleContexts #-}

module G2.Core.Defunctionalizor where

import G2.Core.CoreManipulator
import G2.Core.Language
import G2.Core.Utils

import qualified Data.List as L
import qualified Data.Map  as M

import qualified Data.Monoid as Mon

{-Defunctionalizor

We need to eliminate higher order functions to
enable a translation to SMT formulas.

This can be done via Defunctionalization, described by Reynolds in
http://cs.au.dk/~hosc/local/HOSC-11-4-pp363-397.pdf

In short, each call to a higher order functions (a -> b) -> c is identified.
For each a, b pair, a new datatype A_B, and fresh function, apply_a_b :: A_B -> a -> b, is created.
-}

type FuncName = Name
type DataName = Name


defunctionalize :: Expr -> Expr
defunctionalize e = e


-- appliesFuncsAndTypes :: State -> State
-- appliesFuncsAndTypes (tv, env, ex, pc) =
--     let
--         funcsData = leadingHigherOrderFuncTypesToApplies e
--     in

--Returns all Vars with the given Name
findFuncVar :: (Manipulatable Expr m) => Name -> m -> [Expr]
findFuncVar n e = eval (findFuncVar' n) e
    where
        findFuncVar' :: Name -> Expr -> [Expr]
        findFuncVar' n v@(Var n' t) = [v]
        findFuncVar _ _ = []

--This returns a mapping from all higher order function types to
--names for cooresponding Apply functions and data types
leadingHigherOrderFuncTypesToApplies :: (Manipulatable Expr m) => m -> [(Type, (FuncName, DataName))]
leadingHigherOrderFuncTypesToApplies e =
    let
        h = L.nub . map typeOf . findLeadingHigherOrderFuncs $ e
        bv = freeVars [] e
        funcN = numFresh "apply" (length h) bv
        funcD = numFresh "apply" (length h) (bv ++ funcN)
    in 
    zip h . zip funcN $ funcD

--returns all expressions of the form (a -> b) -> c in the given expr
findLeadingHigherOrderFuncs :: (Manipulatable Expr m) => m -> [Expr]
findLeadingHigherOrderFuncs e = filter (isLeadingHigherOrderFuncType . typeOf) (findHigherOrderFuncs e)

--returns all expressions corresponding to higher order functions in the given expr
findHigherOrderFuncs :: (Manipulatable Expr m) => m -> [Expr]
findHigherOrderFuncs e = L.nub . evalTypesInExpr (\e' t -> if isHigherOrderFuncType t then [e'] else []) e $ []

isHigherOrderFuncType :: Type -> Bool
isHigherOrderFuncType (TyFun t1 t2) = Mon.getAny . eval (Mon.Any . isLeadingHigherOrderFuncType) $ (TyFun t1 t2)
isHigherOrderFuncType _ = False

isLeadingHigherOrderFuncType :: Type -> Bool
isLeadingHigherOrderFuncType (TyFun (TyFun _ _) _) = True
isLeadingHigherOrderFuncType _ = False