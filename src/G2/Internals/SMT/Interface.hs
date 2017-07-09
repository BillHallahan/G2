{-# LANGUAGE FlexibleContexts #-}

module G2.Internals.SMT.Interface ( satModelOutputs
                                  , satModelOutput
                                  , smtReady) where

import Data.List
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Monoid as Mon

import G2.Internals.Core
import G2.Internals.SMT.Converters
import G2.Internals.SMT.Language

-- | satModelOutput
-- Given an smt converter and a list of states, checks if each is satisfiable.
-- Returns a list of possible input/output pairs for the satisifiable states
satModelOutputs :: SMTConverter ast out io -> io -> [State] -> IO [([Expr], Expr)]
satModelOutputs con io s = do
   let s' = smtReady s

   return . map (\(s, es, e) -> (fromJust es, fromJust e))
          . filter (\(s, es, e) -> s == SAT && isJust es && isJust e)
          =<< mapM (satModelOutput con io) s'

-- | checkSatModelOutput
-- Given an smt converter and a list state, checks if the states current expression
-- and path constraints are satisfiable.  If they are, one possible input and output
-- are also returned
satModelOutput :: SMTConverter ast out io -> io -> State -> IO (Result, Maybe [Expr], Maybe Expr)
satModelOutput con io s = do
    let headers = toSMTHeaders s
    let formula = toSolver con headers
    let vars = sltToSMTNameSorts $ sym_links s

    (res, m, ex) <- checkSatGetModelGetExpr con io formula headers vars (curr_expr s)

    -- Determine the input
    let inArg = case (fmap (replaceFuncSLT s . modelAsExpr) m) of
            Just m' -> 
                    let argOrder = map (\(n, _, _) -> n)
                                   . sortOn (\(_, _, x) -> fromJust x)
                                   . filter (\(_, _, x) -> isJust x) 
                                   . M.elems $ sym_links s in
                    Just $ map (\n -> fromJust $ M.lookup n m') argOrder
            Nothing -> Nothing

    -- Convert the output to an expression
    let ex' = fmap (replaceFuncSLT s . smtastToExpr) ex

    return (res, inArg, ex')

-- | smtReady
-- Given a list of states, returns only those that can be evaluated by the SMT solver
smtReady :: [State] -> [State]
smtReady = filter (\s -> not . containsNonConsFunctions (type_env s) . curr_expr $ s)
         . filter (\s -> not . containsBadExpr . curr_expr $ s)

-- Returns if an Expr contains functions that are not just type constructors
containsNonConsFunctions :: (ASTContainer m Expr) => TEnv -> m -> Bool
containsNonConsFunctions tenv = Mon.getAny . evalASTs (Mon.Any . containsFunctions' tenv)
    where
        containsFunctions' :: TEnv -> Expr -> Bool
        containsFunctions' tenv (App (Var n _) _) = n `notElem` (constructors tenv)
        containsFunctions' _ _ = False

        constructors :: TEnv -> [Name]
        constructors = evalASTs constructors'
            where
                constructors' :: Type -> [Name]
                constructors' (TyAlg _ dc) = [ n | (DataCon n _ _ _) <- dc]
                constructors' _ = []

-- Returns true if an Expr contains any Expr that can't be handled by the SMT solver
containsBadExpr :: (ASTContainer m Expr) => m -> Bool
containsBadExpr = Mon.getAny . evalASTs (Mon.Any . containsBadExpr')
    where
        containsBadExpr' :: Expr -> Bool
        containsBadExpr' (Var _ _) = False
        containsBadExpr' (Prim _ _) = False
        containsBadExpr' (Const _) = False
        containsBadExpr' (App _ _) = False
        containsBadExpr' (Data _) = False
        containsBadExpr' (Type _) = False
        containsBadExpr' _ = True

-- TODO: MOVE THE BELOW FUNCTION

--Switches every occurence of a Var in the Func SLT from datatype to function
replaceFuncSLT :: ASTContainer m Expr => State -> m -> m
replaceFuncSLT s e = modifyASTs replaceFuncSLT' e
    where
        replaceFuncSLT' :: Expr -> Expr
        replaceFuncSLT' v@(Var n t) =
            let
                n' = M.lookup n (func_interps s)
            in
            case n' of
                    Just (n'', _) -> Var n'' (case functionType s n'' of
                                                Just t -> t
                                                Nothing -> TyBottom)
                    Nothing -> v
        replaceFuncSLT' e = e

        functionType :: State -> Name -> Maybe Type
        functionType s n = exprType <$> M.lookup n (expr_env s)