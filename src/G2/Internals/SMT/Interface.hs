module G2.Internals.SMT.Interface
    ( satModelOutputs
    ) where

import qualified Data.Map as M
import Data.Maybe

import G2.Internals.Execution.Rules
import G2.Internals.Language
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
satModelOutput :: SMTConverter ast out io -> io -> State -> IO (Result, Maybe [Expr], Maybe Expr) --IO (Result, Maybe [Expr], Maybe Expr)
satModelOutput con io s = do
    let headers = toSMTHeaders s
    let formula = toSolver con headers
    let vs = map (\(Id n t) -> (nameToStr n, typeToSMT t)) (input_ids s)

    (res, m, ex) <- checkSatGetModelGetExpr con io formula headers vs (expr_env s) (curr_expr s)

    let input = fmap modelAsExpr m

    let input' = case input of 
            Just inp  -> Just $ map (\(Id n _) -> inp M.! n) (input_ids s)
            Nothing -> Nothing

    return (res, input', ex)

-- Remove all types from the type environment that contain a function
filterTEnv :: State -> State
filterTEnv s@State {type_env = tenv} = s {type_env = M.filter filterTEnv' tenv}

filterTEnv' :: AlgDataTy -> Bool
filterTEnv' (AlgDataTy _ dc) = not $ any filterTEnv'' dc

filterTEnv'' :: DataCon -> Bool
filterTEnv'' (DataCon _ _ ts) = any (hasFuncType) ts
filterTEnv'' _ = False

{- TODO: This function is hacky- would be better to correctly handle typeclasses... -}
simplifyPrims :: ASTContainer t Expr => t -> t
simplifyPrims = modifyASTs simplifyPrims'

simplifyPrims' :: Expr -> Expr
simplifyPrims' (App (App (App (Prim Negate t) _) _) a) = App (Prim Negate t) a
simplifyPrims' (App (App (App (App (Prim p t) _) _) a) b) = App (App (Prim p t) a) b
simplifyPrims' e = e
