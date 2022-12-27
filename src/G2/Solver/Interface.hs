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

import Data.Function
import qualified Data.List as L
import Data.Maybe (mapMaybe)
import qualified Data.HashMap.Lazy as HM

subModel :: State t -> Bindings -> ([Expr], Expr, Maybe FuncCall)
subModel (State { expr_env = eenv
                , curr_expr = CurrExpr _ cexpr
                , assert_ids = ais
                , type_classes = tc
                , model = m}) 
          (Bindings {input_names = inputNames}) = 
    let
        ais' = fmap (subVarFuncCall True m eenv tc) ais

        -- We do not inline Lambdas, because higher order function arguments
        -- get preinserted into the model.
        -- See [Higher-Order Model] in G2.Execution.Reducers
        is = mapMaybe (\n -> case E.lookup n eenv of
                                Just e@(Lam _ _ _) -> Just . Var $ Id n (typeOf e)
                                Just e -> Just e
                                Nothing -> Nothing) inputNames
    in
    untilEq (simplifyLams . pushCaseAppArgIn) $ subVar True m eenv tc (is, cexpr, ais')
    where
        untilEq f x = let x' = f x in if x == x' then x' else untilEq f x'

subVarFuncCall :: Bool -> Model -> ExprEnv -> TypeClasses -> FuncCall -> FuncCall
subVarFuncCall inLam em eenv tc fc@(FuncCall {arguments = ars}) =
    subVar inLam em eenv tc $ fc {arguments = filter (not . isTC tc) ars}

subVar :: (ASTContainer m Expr) => Bool -> Model -> ExprEnv -> TypeClasses -> m -> m
subVar inLam em eenv tc = modifyContainedASTs (subVar' inLam em eenv tc [])

subVar' :: Bool -> Model -> ExprEnv -> TypeClasses -> [Id] -> Expr -> Expr
subVar' inLam em eenv tc is v@(Var i@(Id n _))
    | i `notElem` is
    , Just e <- HM.lookup n em =
        subVar' inLam em eenv tc (i:is) e
    | i `notElem` is
    , Just e <- E.lookup n eenv
    , (isExprValueForm eenv e && (notLam e || inLam)) || isApp e || isVar e || isLitCase e =
        subVar' inLam em eenv tc (i:is) e
    | otherwise = v
subVar' inLam mdl eenv tc is cse@(Case e _ _ as) =
    case subVar' inLam mdl eenv tc is e of
        Lit l
            | Just (Alt _ ae) <- L.find (\(Alt (LitAlt l') _) -> l == l') as ->
                subVar' inLam mdl eenv tc is ae
        _ -> modifyChildren (subVar' inLam mdl eenv tc is) cse
subVar' inLam em eenv tc is e = modifyChildren (subVar' inLam em eenv tc is) e

isApp :: Expr -> Bool
isApp (App _ _) = True
isApp _ = False

notLam :: Expr -> Bool
notLam (Lam _ _ _) = False
notLam _ = True

isVar :: Expr -> Bool
isVar (Var _) = True
isVar _ = False

isLitCase :: Expr -> Bool
isLitCase (Case e _ _ _) = isPrimType (typeOf e)
isLitCase _ = False

isTC :: TypeClasses -> Expr -> Bool
isTC tc (Var (Id _ (TyCon n _))) = isTypeClassNamed n tc
isTC _ _ = False

-- | Rewrites a case statement returning a function type, and applied to a variable argument,
-- so that the variable argument is moved into each branch of the case statement.
-- This composes with `simplifyLams` to get better simplication for symbolic function concretizations.
pushCaseAppArgIn :: ASTContainer c Expr => c -> c
pushCaseAppArgIn = modifyASTs pushCaseAppArgIn'

pushCaseAppArgIn' :: Expr -> Expr
pushCaseAppArgIn' (App (Case scrut bind t as) v@(Var _)) =
    Case scrut bind t $ map (\(Alt am e) -> Alt am (App e v) ) as
pushCaseAppArgIn' e = e
