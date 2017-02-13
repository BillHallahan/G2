module G2.Core.Defunctionalizor where

import G2.Core.CoreManipulator
import G2.Core.Language

import qualified Data.List as L
import qualified Data.Map  as M

{-Defunctionalizor

We need to eliminate higher order functions to
enable a translation to SMT formulas.

This can be done via Defunctionalization, described by Reynolds in
http://cs.au.dk/~hosc/local/HOSC-11-4-pp363-397.pdf

In short, each call to a higher order functions (a -> b) -> c is identified.
For each a, b pair, a new datatype A_B, and fresh function, apply_a_b :: A_B -> a -> b, is created.
-}


defunctionalize :: Expr -> Expr
defunctionalize e = e


countExpr :: Expr -> Int
countExpr e = evalExpr (\_ -> 1) (+) e 0

countTypes :: Expr -> Int
countTypes e = evalTypesInExpr (\_ -> 1) (+) e 0

-- mkApply :: Name -> Name -> Name-> Type -> Type -> (Expr, Type)
-- mkApply n1 n2 t1 t2 = 
--     let 
--         e = mkApplyFunc
--     in
--     (Lam n e (TyFun t1 t2), )
--     where
--         mkApplyFunc :: Name -> Expr -> Expr
--         mkApplyFunc 

--         mkApplyDataType :: Name -> Name -> Type
--         mkApplyDataType 

findHigherOrderFuncs :: Expr -> [Expr]
findHigherOrderFuncs e = evalTypesInExpr' (\e' t -> if isHigherOrderFuncType t then [e'] else []) (++) e []

--Takes e e1 e2.  Replaces all occurences of e1 in e with e2
replaceExpr :: Expr -> Expr -> Expr -> Expr
replaceExpr e e1 e2 = modifyExpr (replaceCallingSites' e1 e2) e
    where
        replaceCallingSites' :: Expr -> Expr -> Expr -> Expr
        replaceCallingSites' e1 e2 e = if e1 == e then e2 else e

isHigherOrderFuncType :: Type -> Bool
isHigherOrderFuncType (TyFun t1 t2) = evalType (isHigherOrderFuncType') (||) (TyFun t1 t2) False
    where
        isHigherOrderFuncType' :: Type -> Bool
        isHigherOrderFuncType' (TyFun (TyFun _ _) _) = True
        isHigherOrderFuncType' _ = False
isHigherOrderFuncType _ = False