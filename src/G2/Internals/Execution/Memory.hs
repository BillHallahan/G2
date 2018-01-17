module G2.Internals.Execution.Memory 
  ( markAndSweep
  ) where

import G2.Internals.Language.Syntax
import G2.Internals.Language.Support
import G2.Internals.Language.Naming
import G2.Internals.Language.ExprEnv as E

import qualified Data.List as L
import qualified Data.Set as S
import qualified Data.Map as M
import qualified Data.Maybe as B

markAndSweep :: State -> State
markAndSweep state @ State { expr_env = expr_env
                           , type_env = type_env
                           , curr_expr = curr_expr
                           , name_gen = name_gen
                           , path_conds = path_conds
                           , true_assert = true_assert
                           , type_classes = type_classes
                           , sym_links = sym_links
                           , input_ids = input_ids
                           , func_table = func_table
                           , deepseq_walkers = deepseq_walkers
                           , polypred_walkers = polypred_walkers
                           , wrappers = wrappers
                           , apply_types = apply_types
                           , exec_stack = exec_stack
                           , model = model
                           , arbValueGen = arbValueGen
                           , known_values = known_values
                           , cleaned_names = cleaned_names
                           } = state'
  where
    state' = state { expr_env = expr_env'
                   , type_env = type_env'
                   , deepseq_walkers = deepseq_walkers'
                   , polypred_walkers = polypred_walkers'
                   , cleaned_names = cleaned_names'
                   }

    active = activeNames type_env expr_env S.empty $ names curr_expr ++
                                                     names exec_stack ++
                                                     names path_conds

    isActive :: Name -> Bool
    isActive = (flip S.member) active

    expr_env' = E.filterWithKey (\n _ -> isActive n) expr_env
    type_env' = M.filterWithKey (\n _ -> isActive n) type_env

    deepseq_walkers' = M.filterWithKey (\n _ -> isActive n) deepseq_walkers
    polypred_walkers' = M.filterWithKey (\n _ -> isActive n) polypred_walkers

    cleaned_names' = M.empty

activeNames :: TypeEnv -> ExprEnv -> S.Set Name -> [Name] -> S.Set Name
activeNames tenv eenv explored [] = explored
activeNames tenv eenv explored (n:ns) =
    if S.member n explored
      then activeNames tenv eenv explored ns
      else activeNames tenv eenv explored' ns'
  where
    explored' = S.insert n explored
    tenv_hits = case M.lookup n tenv of
        Nothing -> []
        Just r -> names r
    eenv_hits = case E.lookup n eenv of
        Nothing -> []
        Just r -> names r
    ns' = ns ++ tenv_hits ++ eenv_hits

