-- | Configuration
--   Module for interacting and interfacing with the symbolic execution engine.
module G2.Internals.Symbolic.Configuration
    ( initState
    , initStateCond
    , runN
    , histN         ) where

import G2.Internals.Core
import G2.Internals.Symbolic.Engine

import qualified Data.Map as M

-- | Lambda Arguments
--   Strips away the lambda function's arguments.
lamArgs :: Expr -> [(Name, Type)]
lamArgs (Lam n e (TyFun t _)) = (n, t):lamArgs e
lamArgs _ = []

-- | Fresh Argument Names
--   Gets fresh argument names based on the expression environment.
freshArgNames :: EEnv -> Name -> [(Name, Type)]
freshArgNames eenv entry = zip arg_names arg_types
  where entry_expr = case (lookupExpr entry eenv) of
            Just ex -> ex
            Nothing -> error "Entry not found"
        args = lamArgs entry_expr
        arg_names = map fst args
        arg_types = map snd args
        fresh_names = freshSeededNameList arg_names fake_state
        fake_state  = State { expr_env     = eenv
                            , type_env     = M.empty
                            , curr_expr    = BAD
                            , path_cons    = []
                            , sym_links    = M.empty
                            , func_interps = M.empty
                            , all_names    = []      }

-- | Make Symbolic Links
--   Construct a the current expression and a symbolic link table given the
--   entry point name, should it exist in the environment.
mkSymLinks :: EEnv -> Name -> [(Name, Type)] -> (Expr, SymLinkTable)
mkSymLinks eenv entry args = (curr_expr, sym_links)
  where entry_expr = case (lookupExpr entry eenv) of
            Just ex -> ex
            Nothing -> error "Entry not found"
        entry_type = exprType entry_expr
        arg_names  = map fst args
        arg_types  = map snd args
        slt_rhs    = zip3 arg_names arg_types (map Just [1..])
        sym_links  = M.fromList (zip arg_names slt_rhs)
        curr_expr  = foldl (\acc (n, t) -> App acc (Var n t))
                           (Var entry entry_type)
                           args

-- | Initialize State
--   Initialize an execution state given its type environment, expression
--   environment, and entry point name.
initState :: TEnv -> EEnv -> Name -> Name -> State
initState tenv eenv mod entry =
    let -- q_entry = mod ++ ".__." ++ entry
        q_entry = entry
        args = freshArgNames eenv q_entry
        (cexpr, slt) = mkSymLinks eenv q_entry args
        pre_state = State { expr_env     = eenv
                          , type_env     = tenv
                          , curr_expr    = cexpr
                          , path_cons    = []
                          , sym_links    = slt
                          , func_interps = M.empty
                          , all_names    =         []}
        all_names = allNames pre_state
    in pre_state {all_names = all_names}

-- | Flatten Type
--   Flattens a Type. For instance:
--       a -> b -> c  flattens to  [a, b, c]
flattenType :: Type -> [Type]
flattenType (TyFun tf ta) = tf : flattenType ta
flattenType _ = []

-- | Initialize State with Conditionals
--   Initialize an execution state given its type environment, expression
--   environment, and entry point name in addition to pre/post conditional
--   functions that return boolean values.
initStateCond :: TEnv -> EEnv -> Name -> Name -> Name -> State
initStateCond tenv eenv mod cond entry = case match of
    (Just entry_ex, Just cond_ex) -> 
        let args' = freshArgNames eenv q_entry
            (cond_ex', slt) = mkSymLinks eenv q_cond args'
            cond_type  = exprType cond_ex
            entry_type = exprType entry_ex
            (expr', slt') = mkSymLinks eenv q_entry args'
        in if (flattenType entry_type) == (init $ flattenType cond_type)
            then let pre_state = State { expr_env     = eenv
                                       , type_env     = tenv
                                       -- , curr_expr    = App cond_ex' expr'
                                       , curr_expr    = Assume cond_ex' expr'
                                       , path_cons    = []
                                       , sym_links    = slt
                                       , func_interps = M.empty
                                       , all_names    = []      }
                     all_names = allNames pre_state
                 in pre_state {all_names = all_names}
            else error "Incorrect function types given." 
    otherwise -> error "No matching entry points. Check spelling?"
  where -- q_cond  = mod ++ ".__." ++ cond
        q_cond = cond
        -- q_entry = mod ++ ".__." ++ entry
        q_entry = entry
        match = (M.lookup q_entry eenv, M.lookup q_cond eenv)


-- | Run n Times
--   Run a state n times through the power of concatMap.
runN :: [State] -> Int -> ([State], Int)
runN states 0 = (states, 0)
runN [] n     = ([], n - 1)
runN states n = runN (concatMap (\s -> step s) states) (n - 1)

-- | History n Times
--   Run a state n times, while keeping track of its history as a list.
histN :: [State] -> Int -> [([State], Int)]
histN states 0 = [(states, 0)]
histN [] n     = [([], n - 1)]
histN states n = (states', n):(histN states' (n - 1))
  where states' = concatMap step states

