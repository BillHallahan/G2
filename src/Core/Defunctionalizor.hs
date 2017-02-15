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


defunctionalize :: Expr -> Expr
defunctionalize e = e


--Takes e e1 e2.  In e, replaces all occurences of e1 with e2
replaceM :: (Manipulatable e m, Eq e) => m -> e -> e -> m
replaceM e e1 e2 = modify (\e' -> if e1 == e' then e2 else e') e

leadingHigherOrderFuncsToApplies :: (Manipulatable Expr m) => m -> [(Expr, Name)]
leadingHigherOrderFuncsToApplies e =
    let
        h = findLeadingHigherOrderFuncs e
        bv = freeVars [] e 
    in 
    zip h . freshList (replicate (length h) "apply") $ bv

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
isLeadingHigherOrderFuncType t@(TyFun (TyFun _ _) _) = True
isLeadingHigherOrderFuncType _ = False