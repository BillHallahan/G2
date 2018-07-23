{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module G2.Internals.Solver.Interface
    ( subModel
    , subVar
    , subVarFuncCall
    , SMTConverter (..)
    , Solver (..)
    ) where

import G2.Internals.Execution.NormalForms
import G2.Internals.Language
import qualified G2.Internals.Language.ApplyTypes as AT
import qualified G2.Internals.Language.ExprEnv as E
import qualified G2.Internals.Language.PathConds as PC
import G2.Internals.Solver.ADTSolver
import G2.Internals.Solver.Converters
import G2.Internals.Solver.Language
import G2.Internals.Solver.SMT2
import G2.Internals.Solver.Solver

import qualified Data.Map as M
import Data.Maybe

subModel :: State t -> ([Expr], Expr, Maybe FuncCall)
subModel (State { expr_env = eenv
                , curr_expr = CurrExpr _ cexpr
                , input_ids = is
                , assert_ids = ais
                , type_classes = tc
                , model = m}) =
    let
        ais' = fmap (subVarFuncCall m eenv tc) ais
    in
    filterTC tc $ subVar m eenv tc (map Var is, cexpr, ais')

subVarFuncCall :: Model -> ExprEnv -> TypeClasses -> FuncCall -> FuncCall
subVarFuncCall em eenv tc fc@(FuncCall {arguments = ars}) =
    subVar em eenv tc $ fc {arguments = filter (not . isTC tc) ars}

subVar :: (ASTContainer m Expr) => Model -> ExprEnv -> TypeClasses -> m -> m
subVar em eenv tc = modifyContainedASTs (subVar' em eenv tc []) . filterTC tc

subVar' :: Model -> ExprEnv -> TypeClasses -> [Id] -> Expr -> Expr
subVar' em eenv tc is v@(Var i@(Id n _))
    | i `notElem` is =
    case M.lookup n em of
        Just e -> subVar' em eenv tc (i:is) $ filterTC tc e
        Nothing -> case E.lookup n eenv of
            Just e -> if (isExprValueForm e eenv && notLam e) || isApp e || isVar e
                        then subVar' em eenv tc (i:is) $ filterTC tc e
                        else v
            Nothing -> v
    | otherwise = v
subVar' em eenv tc is e = modifyChildren (subVar' em eenv tc is) e

notLam :: Expr -> Bool
notLam (Lam _ _) = False
notLam _ = True

isApp :: Expr -> Bool
isApp (App _ _) = True
isApp _ = False

isVar :: Expr -> Bool
isVar (Var _) = True
isVar _ = False

filterTC :: ASTContainer m Expr => TypeClasses -> m -> m
filterTC tc = modifyASTsFix (filterTC' tc)

filterTC' :: TypeClasses -> Expr -> Expr
filterTC' tc a@(App e e') =
    case tcCenter tc $ typeOf e' of
        True -> e 
        False -> a
filterTC' _ e = e

tcCenter :: TypeClasses -> Type -> Bool
tcCenter tc (TyConApp n _) = isTypeClassNamed n tc
tcCenter tc (TyFun t _) = tcCenter tc t
tcCenter _ _ = False

isTC :: TypeClasses -> Expr -> Bool
isTC tc (Var (Id _ (TyConApp n _))) = isTypeClassNamed n tc
isTC _ _ = False