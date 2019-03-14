module G2.Execution.Memory 
  ( markAndSweep
  , markAndSweepPreserving
  ) where

import G2.Language.Syntax
import G2.Language.Support
import G2.Language.Naming
import G2.Language.ExprEnv as E

import qualified Data.HashSet as S
import qualified Data.Map as M

markAndSweep :: State t -> Bindings -> (State t, Bindings)
markAndSweep = markAndSweepPreserving []

markAndSweepPreserving :: [Name] -> State t -> Bindings -> (State t, Bindings)
markAndSweepPreserving ns (state@State { expr_env = eenv
                                       , type_env = tenv
                                       , curr_expr = cexpr
                                       , path_conds = pc
                                       , symbolic_ids = iids
                                       , exec_stack = es
                                       , known_values = kv
                                       }) (bindings@Bindings {deepseq_walkers = dsw}) = -- error $ show $ length $ take 20 $ PC.toList path_conds
                               (state', bindings')
  where
    state' = state { expr_env = eenv'
                   , type_env = tenv'
                   }
    bindings' = bindings { deepseq_walkers = dsw'}

    active = activeNames tenv eenv S.empty $ names cexpr ++
                                                   names es ++
                                                   names pc ++
                                                   names kv ++
                                                   names iids ++
                                                   ns

    isActive :: Name -> Bool
    isActive = (flip S.member) active

    eenv' = E.filterWithKey (\n _ -> isActive n) eenv
    tenv' = M.filterWithKey (\n _ -> isActive n) tenv

    dsw' = M.filterWithKey (\n _ -> isActive n) dsw

activeNames :: TypeEnv -> ExprEnv -> S.HashSet Name -> [Name] -> S.HashSet Name
activeNames _ _ explored [] = explored
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
    ns' = tenv_hits ++ eenv_hits ++ ns

