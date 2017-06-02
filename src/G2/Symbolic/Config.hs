module G2.Symbolic.Config where

import qualified Data.Map as M

import G2.Lib.Utils

import G2.Core.Language
import G2.Core.Utils
import G2.Symbolic.Engine

-- | Lambda Arguments
--   Stripes away the lambda function's arguments.
lamArgs :: Expr -> [(Name, Type)]
lamArgs (Lam n e (TyFun t _)) = (n, t):lamArgs e
lamArgs _ = []

freshArgNames :: EEnv -> Name -> [(Name, Type)]
freshArgNames eenv entry = zip arg_names arg_types
  where entry_expr = batman (lookupExpr entry eenv) "Entry not found."
        args = lamArgs entry_expr
        arg_names = map fst args
        arg_types = map snd args
        fresh_names = freshSeededNameList arg_names fake_state
        fake_state = State { expr_env     = eenv
                           , type_env     = M.empty
                           , curr_expr    = BAD
                           , path_cons    = []
                           , sym_links    = M.empty
                           , func_interps = M.empty }

-- | Lambda Bindings
--   Construct a the current expression and a symbolic link table given the
--   entry point name, should it exist in the environment.
mkSymLinks :: EEnv -> Name -> [(Name, Type)] -> (Expr, SymLinkTable)
mkSymLinks eenv entry args = (curr_expr, sym_links)
  where entry_expr = batman (lookupExpr entry eenv) "Entry not found."
        entry_type = exprType entry_expr
        arg_names  = map fst args
        arg_types  = map snd args
        slt_rhs    = zip3 arg_names arg_types (map Just [1..])
        sym_links  = M.fromList (zip arg_names slt_rhs)
        curr_expr  = foldl (\acc (n,t) -> App acc (Var n t))
                           (Var entry entry_type) args

{-
-- Just in case I, Anton, fucked something up when refactoring the above.
mkSymLinks :: EEnv -> Name -> [(Name, Type)] -> (Expr, SymLinkTable)
mkSymLinks e_env n nfs = 
    let 
        ex = case M.lookup n e_env of
                    Nothing -> error "No matching entry point. Check spelling?"
                    Just ex' -> ex'
        ty = exprType ex
        nfs' = map fst nfs
        types = map snd nfs
        slt = M.fromList . zip nfs' . zip3 nfs' types $ map Just [1..]
     in
     (foldl (\ex' (n, t) -> App ex' (Var n t)) (Var n ty) . zip nfs' $ types, slt)
-}

-- | Initialize State
--   Initialize an execution state given its type environment, expression
--   environment, and entry point name.
initState :: TEnv -> EEnv -> Name -> State
initState tenv eenv entry = let args' = freshArgNames eenv entry
                                (cexpr, slt) = mkSymLinks eenv entry args'
                            in State { expr_env     = eenv
                                     , type_env     = tenv
                                     , curr_expr    = cexpr
                                     , path_cons    = []
                                     , sym_links    = slt
                                     , func_interps = M.empty }


{-
initStateWithPost :: TEnv -> EEnv -> Name -> Name -> State
initStateWithPost tenv eenv post entry = undefined
-}
initStateWithPost :: TEnv -> EEnv -> Name -> Name -> State
initStateWithPost t_env e_env post entry =
    case match of
        (Just entry_ex, Just post_ex) -> 
                    let
                        newArgs = freshArgNames e_env entry
                        (post_ex', slt) = mkSymLinks e_env post newArgs
                        entry_type = exprType entry_ex
                        post_type = exprType post_ex
                        (expr', slt') = mkSymLinks e_env entry newArgs
                    in
                    if addToBool entry_type == post_type then
                        State t_env e_env (App post_ex' expr') [] slt M.empty
                    else
                        error "Incorrect function types given." 
        otherwise -> error "No matching entry points. Check spelling?"
    where
        match = (M.lookup entry e_env, M.lookup post e_env)

        addToBool :: Type -> Type
        addToBool (TyFun t t') = TyFun t (addToBool t')
        addToBool t = TyFun t (TyConApp "Bool" [])

runN :: [State] -> Int -> ([State], Int)
runN states 0 = (states, 0)
runN [] n     = ([], n - 1)
runN states n = runN (concatMap (\s -> step s) states) (n - 1)

histN :: [State] -> Int -> [([State], Int)]
histN states 0 = [(states, 0)]
histN [] n     = [([], n - 1)]
histN states n = let states' = concatMap step states
                 in (states', n):histN states' (n - 1)

