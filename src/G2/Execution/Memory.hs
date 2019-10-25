{-# LANGUAGE RankNTypes #-}

module G2.Execution.Memory 
  ( MemConfig (..)
  , emptyMemConfig
  , addSearchNames
  , markAndSweep
  , markAndSweepIgnoringKnownValues
  , markAndSweepPreserving
  ) where

import G2.Language.Syntax
import G2.Language.Support
import G2.Language.Naming
import qualified G2.Language.ExprEnv as E
import G2.Language.Typing

import Data.List
import qualified Data.HashSet as S
import qualified Data.Map as M

type PreservingFunc = forall t . State t -> Bindings -> S.HashSet Name -> S.HashSet Name

data MemConfig = MemConfig { search_names :: [Name]
                           , pres_func :: PreservingFunc }

instance Monoid MemConfig where
    mempty = MemConfig { search_names = [], pres_func = \ _ _ hs -> hs }

    mappend (MemConfig { search_names = sn1, pres_func = pf1 })
            (MemConfig { search_names = sn2, pres_func = pf2 }) =
                MemConfig { search_names = sn1 ++ sn2
                          , pres_func = \s b hs -> pf1 s b $ pf2 s b hs}

emptyMemConfig :: MemConfig
emptyMemConfig = MemConfig { search_names = [], pres_func = \_ _ a -> a }

markAndSweep :: State t -> Bindings -> (State t, Bindings)
markAndSweep s = markAndSweepPreserving emptyMemConfig s

addSearchNames :: [Name] -> MemConfig -> MemConfig
addSearchNames ns mc@(MemConfig { search_names = ns' }) = mc { search_names = ns ++ ns'}

markAndSweepIgnoringKnownValues :: State t -> Bindings -> (State t, Bindings)
markAndSweepIgnoringKnownValues = markAndSweepPreserving' emptyMemConfig

markAndSweepPreserving :: MemConfig -> State t -> Bindings -> (State t, Bindings)
markAndSweepPreserving mc s =
    markAndSweepPreserving' (names (known_values s) `addSearchNames` mc) s

markAndSweepPreserving' :: MemConfig -> State t -> Bindings -> (State t, Bindings)
markAndSweepPreserving' mc (state@State { expr_env = eenv
                                        , type_env = tenv
                                        , curr_expr = cexpr
                                        , path_conds = pc
                                        , symbolic_ids = iids
                                        , exec_stack = es
                                        }) (bindings@Bindings { deepseq_walkers = dsw
                                                              , higher_order_inst = inst }) = -- error $ show $ length $ take 20 $ PC.toList path_conds
                               (state', bindings')
  where
    state' = state { expr_env = eenv'
                   , type_env = tenv'
                   }
    bindings' = bindings { deepseq_walkers = dsw'}

    active = activeNames tenv (E.redirsToExprs eenv) S.empty $ names cexpr ++
                                                               names es ++
                                                               names pc ++
                                                               names iids ++
                                                               higher_ord_rel ++
                                                               search_names mc

    active' = S.union (pres_func mc state bindings active) active

    isActive :: Name -> Bool
    isActive = (flip S.member) active'

    eenv' = E.filterWithKey (\n _ -> isActive n) eenv
    tenv' = M.filterWithKey (\n _ -> isActive n) tenv

    dsw' = M.filterWithKey (\n _ -> isActive n) dsw

    higher_ord_eenv = E.filterWithKey (\n _ -> n `elem` inst) eenv
    higher_ord = map PresType $ nubBy (.::.) $ argTypesTEnv tenv ++ E.higherOrderExprs higher_ord_eenv
    higher_ord_rel = E.keys $ E.filter (\e -> any (.:: typeOf e) higher_ord) higher_ord_eenv

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

