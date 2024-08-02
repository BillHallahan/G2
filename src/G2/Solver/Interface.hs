{-# LANGUAGE FlexibleContexts, MultiParamTypeClasses, OverloadedStrings, TupleSections #-}

module G2.Solver.Interface
    ( Subbed (..)
    , subModel
    , subVar
    , subVarFuncCall
    , SMTConverter (..)
    , Solver (..)
    ) where

import G2.Execution.NormalForms
import G2.Language
import qualified G2.Language.ExprEnv as E
import G2.Language.MutVarEnv
import G2.Solver.Converters
import G2.Solver.Solver

import qualified Data.List as L
import Data.Maybe (mapMaybe, isJust, fromJust)
import qualified Data.HashMap.Lazy as HM
import qualified Data.Sequence as S

-- | Concrete instantiations of previously (partially) symbolic values.
data Subbed = Subbed { s_inputs :: [Expr] -- ^ Concrete `inputNames`
                     , s_output :: Expr -- ^ Concrete `curr_expr`
                     , s_violated :: Maybe FuncCall -- ^ Concrete `assert_ids`
                     , s_sym_gens :: S.Seq Expr -- ^ Concrete `sym_gens`
                     , s_mutvars :: [(Name, Expr)] -- ^ Concrete symbolic `mutvar_env`
                     }
                     deriving Eq

instance ASTContainer Subbed Expr where
    containedASTs sub =
           s_inputs sub
        ++ s_output sub:containedASTs (s_violated sub)
        ++ containedASTs (s_sym_gens sub)
        ++ containedASTs (s_mutvars sub)
    modifyContainedASTs f sub =
        Subbed { s_inputs = map f (s_inputs sub)
               , s_output = f (s_output sub)
               , s_violated = modifyContainedASTs f (s_violated sub)
               , s_sym_gens = modifyContainedASTs f (s_sym_gens sub)
               , s_mutvars = modifyContainedASTs f (s_mutvars sub) }

instance ASTContainer Subbed Type where
    containedASTs sub =
           containedASTs (s_inputs sub)
        ++ containedASTs (s_output sub)
        ++ containedASTs (s_violated sub)
        ++ containedASTs (s_sym_gens sub)
        ++ containedASTs (s_mutvars sub)
    modifyContainedASTs f sub =
        Subbed { s_inputs = modifyContainedASTs f (s_inputs sub)
               , s_output = modifyContainedASTs f (s_output sub)
               , s_violated = modifyContainedASTs f (s_violated sub)
               , s_sym_gens = modifyContainedASTs f (s_sym_gens sub)
               , s_mutvars = modifyContainedASTs f (s_mutvars sub) }

subModel :: State t -> Bindings -> Subbed
subModel (State { expr_env = eenv
                , curr_expr = CurrExpr _ cexpr
                , assert_ids = ais
                , type_classes = tc
                , model = m
                , sym_gens = gens
                , mutvar_env = mve }) 
          (Bindings {input_names = inputNames}) = 
    let
        ais' = fmap (subVarFuncCall True m eenv tc) ais

        -- We do not inline all Lambdas, because higher order function arguments
        -- get preinserted into the model.
        -- See [Higher-Order Model] in G2.Execution.Reducers
        is = mapMaybe toVars inputNames
        gs = fmap fromJust . S.filter isJust $ fmap toVars gens

        mv = mapMaybe (\(n, mvi) -> fmap (n,) . toVars . idName $ mv_val_id mvi) (HM.toList mve)

        sub = Subbed { s_inputs = is
                     , s_output = cexpr
                     , s_violated = ais'
                     , s_sym_gens = gs
                     , s_mutvars = mv }
        
        sv = subVar False m eenv tc sub
    in
    untilEq (simplifyLams . pushCaseAppArgIn) sv
    where
        toVars n = case E.lookup n eenv of
                                Just e@(Lam _ _ _) -> Just . Var $ Id n (typeOf e)
                                Just e -> Just e
                                Nothing -> Nothing

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
    -- We want to inline a lambda only if inLam is true (we want to inline all lambdas),
    -- or if it's module is Nothing (and its name is likely uninteresting/unknown to the user)
    , (isExprValueForm eenv e && (notLam e || inLam || nameModule n == Nothing)) || isApp e || isVar e || isLitCase e =
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
