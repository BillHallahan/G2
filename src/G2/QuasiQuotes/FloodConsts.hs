-- Tries to eliminate a symbolic variable by replacing it with a constant.

module G2.QuasiQuotes.FloodConsts ( floodConstants
                                  , floodConstant) where

import G2.Language
import qualified G2.Language.ExprEnv as E

import Debug.Trace

floodConstants :: [(Name, Expr)] -> State t -> Maybe (State t)
floodConstants ne s = trace "floodConstants" foldr (\(n, e) s' -> floodConstant n e =<< s') (Just s) ne

-- | Tries to eliminate a symbolic variable by replacing them with constants.
-- Returns Maybe a State, if the variable is replacable
floodConstant :: Name -> Expr -> State t -> Maybe (State t)
floodConstant n e s
    | E.isSymbolic n (expr_env s) =
        case trace ("flood 1 n = " ++ show n ++ "\ne = " ++ show e) E.lookup n (expr_env s) of
            Just e' ->
                let
                    i = Id n $ typeOf e'
                    r_pc = replaceASTs (Var i) e (path_conds s) 
                in
                Just (s { expr_env = E.insert n e (expr_env s)
                        , path_conds = r_pc })
            _ -> Nothing
    | otherwise = 
        case trace ("flood 2 n = " ++ show n ++ "\ne = " ++ show e) E.lookup n (expr_env s) of
                Just e'
                    | Data d:es <- unApp e
                    , Data d':es' <- unApp e'
                    , d == d' -> trace ("es  = " ++ show es ++ "\nes' = " ++ show es') floodConstantList s (zip es es')
                _ -> Nothing

floodConstantList :: State t -> [(Expr, Expr)] -> Maybe (State t)
floodConstantList s  ((e1, e2):xs)
    | Var (Id n _) <- e2 =
        (\s' -> floodConstantList s' xs) =<< floodConstant n e1 s
    | e1 == e2 = floodConstantList s xs
floodConstantList s [] = Just s
floodConstantList _ _ = Nothing