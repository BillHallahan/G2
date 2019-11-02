-- Tries to eliminate a symbolic variable by replacing it with a constant.

module G2.QuasiQuotes.FloodConsts ( floodConstantsChecking
                                  , floodConstants
                                  , floodConstant) where

import G2.Execution.PrimitiveEval
import G2.Language
import qualified G2.Language.ExprEnv as E
import qualified G2.Language.PathConds as PC
import qualified Data.HashSet as HS

-- | Tries to eliminate a symbolic variable by replacing them with constants.
-- Returns Maybe a State, if the variables are replacable, and don't make the
-- path constraints obviously false
floodConstantsChecking :: [(Name, Expr)] -> State t -> Maybe (State t)
floodConstantsChecking ne s =
    case floodConstants ne s of
        Just s' ->
            if all (pathCondMaybeSatisfiable (known_values s')) (PC.toList $ path_conds s')
                then Just s'
                else Nothing
        Nothing -> Nothing

-- | Tries to eliminate a symbolic variable by replacing them with constants.
-- Returns Maybe a State, if the variables are replacable
floodConstants :: [(Name, Expr)] -> State t -> Maybe (State t)
floodConstants ne s = foldr (\(n, e) s' -> floodConstant n e =<< s') (Just s) ne

floodConstant :: Name -> Expr -> State t -> Maybe (State t)
floodConstant n e s
    | E.isSymbolic n (expr_env s) =
        case E.lookup n (expr_env s) of
            Just e' ->
                let
                    i = Id n $ typeOf e'
                    r_pc = replaceASTs (Var i) e (path_conds s) 
                in
                Just (s { expr_env = E.insert n e (expr_env s)
                        , path_conds = r_pc
                        , symbolic_ids = HS.delete i (symbolic_ids s)})
            _ -> Nothing
    | otherwise = 
        case E.lookup n (expr_env s) of
                Just e'
                    | Data d:es <- unApp e
                    , Data d':es' <- unApp e'
                    , dcName d == dcName d' -> floodConstantList s (zip es es')
                _ -> Nothing

floodConstantList :: State t -> [(Expr, Expr)] -> Maybe (State t)
floodConstantList s  ((e1, e2):xs)
    | Var (Id n _) <- e2 =
        (\s' -> floodConstantList s' xs) =<< floodConstant n e1 s
    | e1 == e2 = floodConstantList s xs
floodConstantList s [] = Just s
floodConstantList _ _ = Nothing

-- Attempts to determine if a PathCond is satisfiable.  A return value of False
-- means the PathCond is definitely unsatisfiable.  A return value of True means
-- the PathCond may or may not be satisfiable. 
pathCondMaybeSatisfiable :: KnownValues -> PathCond -> Bool
pathCondMaybeSatisfiable _ (AltCond l1 (Lit l2) b) = (l1 == l2) == b
pathCondMaybeSatisfiable _ (AltCond _ _ _) = True
pathCondMaybeSatisfiable kv (ExtCond e b) =
    let
        r = evalPrims kv e
        
        tr = mkBool kv True
        fal = mkBool kv False
    in
    if (r == tr && not b) || (r == fal && b) then False else True
pathCondMaybeSatisfiable _ (AssumePC _ _ _) = True
