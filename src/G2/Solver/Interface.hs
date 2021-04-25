{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module G2.Solver.Interface
    ( subModel
    , subVar
    , subVarFuncCall
    , SMTConverter (..)
    , Solver (..)
    ) where

import G2.Execution.NormalForms
import G2.Language
import qualified G2.Language.ExprEnv as E
import G2.Solver.Converters
import G2.Solver.Solver

import qualified Data.List as L
import Data.Maybe (mapMaybe)
import qualified Data.HashMap.Lazy as HM

import Debug.Trace

subModel :: State t -> Bindings -> ([Expr], Expr, Maybe FuncCall)
subModel (State { expr_env = eenv
                , curr_expr = CurrExpr _ cexpr
                , assert_ids = ais
                , type_classes = tc
                , model = m}) 
          (Bindings {input_names = inputNames}) = 
    let
        ais' = fmap (subVarFuncCall m eenv tc) ais

        -- We do not inline Lambdas, because higher order function arguments
        -- get preinserted into the model.
        -- See [Higher-Order Model] in G2.Execution.Reducers
        is = mapMaybe (\n -> case E.lookup n eenv of
                                Just e@(Lam _ _ _) -> Just . Var $ Id n (typeOf e)
                                Just e -> Just e
                                Nothing -> Nothing) inputNames
    in
    subVar m eenv tc (is, cexpr, ais')

subVarFuncCall :: Model -> ExprEnv -> TypeClasses -> FuncCall -> FuncCall
subVarFuncCall em eenv tc fc@(FuncCall {arguments = ars}) =
    subVar em eenv tc $ fc {arguments = filter (not . isTC tc) ars}

subVar :: (ASTContainer m Expr) => Model -> ExprEnv -> TypeClasses -> m -> m
subVar em eenv tc = modifyContainedASTs (subVar' em eenv tc [])

subVar' :: Model -> ExprEnv -> TypeClasses -> [Id] -> Expr -> Expr
subVar' em eenv tc is v@(Var i@(Id n _))
    | i `notElem` is
    , Just e <- HM.lookup n em =
        subVar' em eenv tc (i:is) e
    | i `notElem` is
    , Just e <- E.lookup n eenv
    , (isExprValueForm eenv e && notLam e) || isApp e || isVar e || isLitCase e =
        subVar' em eenv tc (i:is) e
    | otherwise = v
subVar' mdl eenv tc is cse@(Case e _ as) =
    case subVar' mdl eenv tc is e of
        Lit l
            | Just (Alt _ ae) <- L.find (\(Alt (LitAlt l') _) -> l == l') as ->
                subVar' mdl eenv tc is ae
        _ -> cse
subVar' em eenv tc is e = modifyChildren (subVar' em eenv tc is) e

notLam :: Expr -> Bool
notLam (Lam _ _ _) = False
notLam _ = True

isApp :: Expr -> Bool
isApp (App _ _) = True
isApp _ = False

isVar :: Expr -> Bool
isVar (Var _) = True
isVar _ = False

isLitCase :: Expr -> Bool
isLitCase (Case e _ _) = isPrimType (typeOf e)
isLitCase _ = False

isTC :: TypeClasses -> Expr -> Bool
isTC tc (Var (Id _ (TyCon n _))) = isTypeClassNamed n tc
isTC _ _ = False
