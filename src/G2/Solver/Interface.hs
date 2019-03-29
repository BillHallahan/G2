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

import Data.Maybe (catMaybes)
import qualified Data.Map as M

subModel :: State t -> Bindings -> ([Expr], Expr, Maybe FuncCall)
subModel (State { expr_env = eenv
                , curr_expr = CurrExpr _ cexpr
                , assert_ids = ais
                , type_classes = tc
                , model = m}) 
          (Bindings {input_names = inputNames}) = 
    let
        ais' = fmap (subVarFuncCall m eenv tc) ais
        is = catMaybes (map ((flip E.lookup) eenv) inputNames)
    in
      filterTC tc $ subVar m eenv tc (is, cexpr, ais')

subVarFuncCall :: Model -> ExprEnv -> TypeClasses -> FuncCall -> FuncCall
subVarFuncCall em eenv tc fc@(FuncCall {arguments = ars}) =
    subVar em eenv tc $ fc {arguments = filter (not . isTC tc) ars}

subVar :: (ASTContainer m Expr) => Model -> ExprEnv -> TypeClasses -> m -> m
subVar em eenv tc = modifyContainedASTs (subVar' em eenv tc []) . filterTC tc

subVar' :: Model -> ExprEnv -> TypeClasses -> [Id] -> Expr -> Expr
subVar' em eenv tc is v@(Var i@(Id n _))
    | i `notElem` is
    , Just e <- M.lookup n em =
        subVar' em eenv tc (i:is) $ filterTC tc e
    | i `notElem` is
    , Just e <- E.lookup n eenv
    , (isExprValueForm eenv e && notLam e) || isApp e || isVar e =
        subVar' em eenv tc (i:is) $ filterTC tc e
    -- case M.lookup n em of
    --     Just e -> trace ("e1 = " ++ show e) subVar' em eenv tc (i:is) $ filterTC tc e
    --     Nothing -> case E.lookup n eenv of
    --         Just e -> if (isExprValueForm e eenv && notLam e) || isApp e || isVar e
    --                     then trace ("e2 = " ++ show e) subVar' em eenv tc (i:is) $ filterTC tc e
    --                     else trace ("e3 = " ++ show e) v
    --         Nothing -> trace ("v1 = " ++ show v) v
    | otherwise = v
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

filterTC :: ASTContainer m Expr => TypeClasses -> m -> m
filterTC tc = modifyASTsFix (filterTC' tc)

filterTC' :: TypeClasses -> Expr -> Expr
filterTC' tc a@(App e e') =
    case tcCenter tc $ typeOf e' of
        True -> e 
        False -> a
filterTC' _ e = e

tcCenter :: TypeClasses -> Type -> Bool
tcCenter tc (TyCon n _) = isTypeClassNamed n tc
tcCenter tc (TyFun t _) = tcCenter tc t
tcCenter _ _ = False

isTC :: TypeClasses -> Expr -> Bool
isTC tc (Var (Id _ (TyCon n _))) = isTypeClassNamed n tc
isTC _ _ = False
