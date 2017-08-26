module G2.Internals.SMT.Interface
    ( satModelOutputs
    , satModelOutput
    , smtReady) where

import qualified Data.Map as M
import Data.Maybe
import qualified Data.Monoid as Mon

import G2.Internals.Language
import G2.Internals.SMT.Converters
import G2.Internals.SMT.Language


-- | satModelOutput
-- Given an smt converter and a list of states, checks if each of
-- those that match the criteria of smtReady is satisfiable.
-- Returns a list of possible input/output pairs for the satisifiable states
satModelOutputs :: SMTConverter ast out io -> io -> [State] -> IO [(Model, SMTAST)]--IO [([Expr], Expr)]
satModelOutputs con io s = do
   return . map (\(_, es, e) -> (fromJust es, fromJust e))
          . filter (\(s', es, e) -> s' == SAT && isJust es && isJust e)
          =<< mapM (satModelOutput con io) (smtReady s)


-- | checkSatModelOutput
-- Given an smt converter and a list state, checks if the states current expression
-- and path constraints are satisfiable.  If they are, one possible input and output
-- are also returned
satModelOutput :: SMTConverter ast out io -> io -> State -> IO (Result, Maybe Model, Maybe SMTAST) --IO (Result, Maybe [Expr], Maybe Expr)
satModelOutput con io s = do
    let headers = toSMTHeaders s
    let formula = toSolver con headers
    let vars = map (\(n, t) -> (nameToStr n, t)) . sltToSMTNameSorts $ sym_links s

    (res, m, ex) <- checkSatGetModelGetExpr con io formula headers vars (curr_expr s)

    return (res, m, ex)
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

-- | smtReady
-- Given a list of states, returns only those that can be evaluated by the SMT solver
smtReady :: [State] -> [State]
smtReady = filter (\s -> not . containsNonConsFunctions (type_env s) . curr_expr $ s)
         . filter (\s -> not . containsBadExpr . curr_expr $ s)

-- Returns if an Expr contains functions that are not just type constructors
containsNonConsFunctions :: (ASTContainer m Expr) => TypeEnv -> m -> Bool
containsNonConsFunctions tenv = Mon.getAny . evalASTs (Mon.Any . containsFunctions' tenv)
    where
        containsFunctions' :: TypeEnv -> Expr -> Bool
        containsFunctions' tv (App (Var (Id n _)) _) = n `notElem` (constructors tv)
        containsFunctions' _ _ = False

        constructors :: TypeEnv -> [Name]
        constructors = concat . map constructors' . M.elems
            
        constructors' :: AlgDataTy -> [Name]
        constructors' (AlgDataTy _ dc) = [ n | (DataCon n _ _) <- dc]

-- Returns true if an Expr contains any Expr that can't be handled by the SMT solver
containsBadExpr :: (ASTContainer m Expr) => m -> Bool
containsBadExpr = Mon.getAny . evalASTs (Mon.Any . containsBadExpr')
    where
        containsBadExpr' :: Expr -> Bool
        containsBadExpr' (Var _) = False
        containsBadExpr' (Prim _) = False
        containsBadExpr' (Lit _) = False
        containsBadExpr' (App _ _) = False
        containsBadExpr' (Data _) = False
        containsBadExpr' (Type _) = False
        containsBadExpr' _ = True

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
