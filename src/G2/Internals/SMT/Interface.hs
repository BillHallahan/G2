module G2.Internals.SMT.Interface
    ( satModelOutputs
    ) where

import qualified Data.Map as M
import Data.Maybe
import qualified Data.Monoid as Mon

import G2.Internals.Execution.Rules
import G2.Internals.Language
import G2.Internals.SMT.Converters
import G2.Internals.SMT.Language


-- | satModelOutput
-- Given an smt converter and a list of states, checks if each of
-- those that match the criteria of smtReady is satisfiable.
-- Returns a list of possible input/output pairs for the satisifiable states
satModelOutputs :: SMTConverter ast out io -> io -> [State] -> IO [([Expr], Expr)]--IO [([Expr], Expr)]
satModelOutputs con io s = do
   return . map (\(_, es, e) -> (fromJust es, fromJust e))
          . filter (\(s', es, e) -> s' == SAT && isJust es && isJust e)
          =<< mapM (satModelOutput con io . simplifyPrims) (filter isExecValueForm s)


-- | checkSatModelOutput
-- Given an smt converter and a list state, checks if the states current expression
-- and path constraints are satisfiable.  If they are, one possible input and output
-- are also returned
satModelOutput :: SMTConverter ast out io -> io -> State -> IO (Result, Maybe [Expr], Maybe Expr) --IO (Result, Maybe [Expr], Maybe Expr)
satModelOutput con io s = do
    let headers = toSMTHeaders s
    let formula = toSolver con headers
    let vars = map (\(Id n t) -> (nameToStr n, typeToSMT t)) (input_ids s)

    (res, m, ex) <- checkSatGetModelGetExpr con io formula headers vars (curr_expr s)

    let input = fmap modelAsExpr m

    let input' = case input of 
            Just inp  -> Just $ map (\(Id n _) -> inp M.! n) (input_ids s)
            Nothing -> Nothing

    let ex' = fmap smtastToExpr ex

    return (res, input', ex')
    {-
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

    return (res, inArg, ex') -}


{- TODO: This function is hacky- would be better to correctly handle typeclasses... -}
simplifyPrims :: ASTContainer t Expr => t -> t
simplifyPrims = modifyASTs simplifyPrims'

simplifyPrims' :: Expr -> Expr
simplifyPrims' (App (App (App (App (Prim e) _) _) a) b) = App (App (Prim e) a) b
simplifyPrims' e = e

{-

-- TODO: MOVE THE BELOW FUNCTION

--Switches every occurence of a Var in the Func SLT from datatype to function
replaceFuncSLT :: ASTContainer m Expr => State -> m -> m
replaceFuncSLT s e = modifyASTs replaceFuncSLT' e
    where
        replaceFuncSLT' :: Expr -> Expr
        replaceFuncSLT' v@(Data (DataCon n _ t _)) =
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
        functionType s n = typeOf <$> M.lookup n (expr_env s)
-}
