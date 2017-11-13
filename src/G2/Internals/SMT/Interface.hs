{-# LANGUAGE FlexibleContexts #-}

module G2.Internals.SMT.Interface
    ( satModelOutputs
    , subModel
    , checkConstraints
    , checkAsserts
    , checkModel
    , checkModelAsserts
    ) where

import qualified Data.Map as M
import Data.Maybe

import G2.Internals.Execution.NormalForms
import G2.Internals.Execution.RuleTypes
import G2.Internals.Language hiding (Model)
import qualified G2.Internals.Language.ExprEnv as E
import qualified G2.Internals.Language.PathConds as PC
import G2.Internals.SMT.Converters
import G2.Internals.SMT.Language

-- | satModelOutput
-- Given an smt converter and a list of states, checks if each of
-- those that match the criteria of smtReady is satisfiable.
-- Returns a list of satisifable states, along with possible input/output pairs
satModelOutputs :: SMTConverter ast out io -> io -> [([Rule], State)] -> IO [(State, [Rule], [Expr], Expr)]
satModelOutputs con io states = do
    let states' = filter (isExecValueForm . snd) states
  
    let states'' = map (\(r, s) -> (r, filterTEnv s)) states'

    return . map (\(s, rs, _, es, e) -> (s, rs, fromJust es, fromJust e))
           . filter (\(_, _, res, es, e) -> res == SAT && isJust es && isJust e)
           =<< mapM (\(rs, s) -> do
                            (res, es, e) <- satModelOutput con io $ simplifyPrims s
                            return (s, rs, res, es, e)) states''

-- | checkSatModelOutput
-- Given an smt converter and a list state, checks if the states current expression
-- and path constraints are satisfiable.  If they are, one possible input and output
-- are also returned
satModelOutput :: SMTConverter ast out io -> io -> State -> IO (Result, Maybe [Expr], Maybe Expr)
satModelOutput con io s = do
    let headers = toSMTHeaders s (curr_expr s)
    let formula = toSolver con headers
    let vs = map (\(Id n t) -> (nameToStr n, typeToSMT t)) (input_ids s)

    (res, m, ex) <- checkSatGetModelGetExpr con io formula headers vs (expr_env s) (curr_expr s)

    let input = fmap modelAsExpr m

    let input' = case input of 
            Just inp  -> Just $ map (\(Id n _) -> inp M.! n) (input_ids s)
            Nothing -> Nothing

    return (res, input', ex)

subModel :: State -> ([Expr], Expr)
subModel (State { curr_expr = CurrExpr _ cexpr
                , input_ids = is
                , model = m}) =
    subVar m (map Var is, cexpr)

subVar :: (ASTContainer m Expr) => ExprModel -> m -> m
subVar em = modifyASTs (subVar' em)

subVar' :: ExprModel -> Expr -> Expr
subVar' em v@(Var (Id n _)) =
    case M.lookup n em of
        Just e -> e
        Nothing -> v
subVar' _ e = e

-- | checkConstraints
-- Checks if the path constraints are satisfiable
checkConstraints :: SMTConverter ast out io -> io -> State -> IO Result
checkConstraints con io s = do
    case PC.checkConsistency (type_env s) (path_conds s) of
        Just True ->
            -- do
            -- putStrLn "True"
            return SAT
        Just False ->
            -- do
            -- putStrLn "False"
            return UNSAT
        _ ->
            -- do
            -- putStrLn $ pprPathsStr . PC.toList $ path_conds s
            -- putStrLn "---"
            checkConstraints' con io s

checkConstraints' :: SMTConverter ast out io -> io -> State -> IO Result
checkConstraints' con io s = do
    -- This is to avoid problems with lack of Asserts knocking out states too early
    let s' = if true_assert s then s
              else s {assertions = [ExtCond (Lit (LitBool True)) True]}

    checkConstraints'' con io s'

checkConstraints'' :: SMTConverter ast out io -> io -> State -> IO Result
checkConstraints'' con io s = do
    let s' = filterTEnv . simplifyPrims $ s

    let headers = toSMTHeaders s' ([] :: [Expr])
    let formula = toSolver con headers

    checkSat con io formula

checkAsserts :: SMTConverter ast out io -> io -> State -> IO Result
checkAsserts = checkConstraints'

checkModel :: SMTConverter ast out io -> io -> State -> IO (Result, Maybe ExprModel)
checkModel con io s = do
    -- This is to avoid problems with lack of Asserts knocking out states too early
    let s' = if true_assert s then s
              else s {assertions = [ExtCond (Lit (LitBool True)) True]}

    checkModel' con io s'

-- TODO: Fix the code duplication between checkConstraints, checkAsserts
checkModelAsserts :: SMTConverter ast out io -> io -> State -> IO (Result, Maybe ExprModel)
checkModelAsserts con io s = checkModel' con io s

checkModel' :: SMTConverter ast out io -> io -> State -> IO (Result, Maybe ExprModel)
checkModel' con io s = do
    let s' = filterTEnv . simplifyPrims $ s

    let headers = toSMTHeaders s' ([] :: [Expr])
    let formula = toSolver con headers

    let vs = filter (flip elem (map nameToStr $ E.symbolicKeys $ expr_env s') . fst)
           $ map (\(n, srt) -> (nameToStr n, srt)) . pcVars . PC.toList $ path_conds s'

    (r, m) <- checkSatGetModel con io formula headers vs

    let m' = fmap modelAsExpr m

    return (r, m')

-- Remove all types from the type environment that contain a function
filterTEnv :: State -> State
filterTEnv s@State { type_env = tenv} =
    if tenv == tenv'
      then s { type_env = tenv }
      else filterTEnv (s { type_env = tenv' })
  where
    tenv' = M.filter (filterTEnv' tenv) tenv

filterTEnv' :: TypeEnv -> AlgDataTy -> Bool
filterTEnv' tenv (AlgDataTy _ dc) = length dc > 0 && not (any (filterTEnv'' tenv) dc)

filterTEnv'' :: TypeEnv -> DataCon -> Bool
filterTEnv'' tenv (DataCon _ _ ts) = any (hasFuncType) ts || any (notPresent tenv) ts
filterTEnv'' _ _ = False

notPresent :: TypeEnv -> Type -> Bool
notPresent tenv (TyConApp n _) = n `M.notMember` tenv
notPresent _ _ = False

{- TODO: This function is hacky- would be better to correctly handle typeclasses... -}
simplifyPrims :: ASTContainer t Expr => t -> t
simplifyPrims = modifyASTs simplifyPrims'

simplifyPrims' :: Expr -> Expr
simplifyPrims' (App (App (App (Prim Negate t) _) _) a) = App (Prim Negate t) a
simplifyPrims' (App (App (App (App (Prim p t) _) _) a) b) = App (App (Prim p t) a) b
simplifyPrims' e = e
