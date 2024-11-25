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

import Data.Foldable
import Data.List
import qualified Data.HashSet as HS
import qualified Data.HashMap.Lazy as HM
import qualified Data.Map as M

import qualified Data.Sequence as S

type PreservingFunc = forall t . State t -> Bindings -> HS.HashSet Name -> HS.HashSet Name

data MemConfig = MemConfig { search_names :: [Name]
                           , pres_func :: PreservingFunc }
               | PreserveAllMC

instance Semigroup MemConfig where
    (MemConfig { search_names = sn1, pres_func = pf1 }) <> (MemConfig { search_names = sn2, pres_func = pf2 }) =
                MemConfig { search_names = sn1 ++ sn2
                          , pres_func = \s b hs -> pf1 s b hs `HS.union` pf2 s b hs}
    _ <> _ = PreserveAllMC

instance Monoid MemConfig where
    mempty = MemConfig { search_names = [], pres_func = \ _ _ -> id }

    mappend = (<>)

emptyMemConfig :: MemConfig
emptyMemConfig = MemConfig { search_names = [], pres_func = \_ _ a -> a }

markAndSweep :: State t -> Bindings -> State t
markAndSweep s = markAndSweepPreserving emptyMemConfig s

addSearchNames :: [Name] -> MemConfig -> MemConfig
addSearchNames ns mc@(MemConfig { search_names = ns' }) = mc { search_names = ns ++ ns' }
addSearchNames _ PreserveAllMC = PreserveAllMC

markAndSweepIgnoringKnownValues :: State t -> Bindings -> State t
markAndSweepIgnoringKnownValues = markAndSweepPreserving' emptyMemConfig

markAndSweepPreserving :: MemConfig -> State t -> Bindings -> State t
markAndSweepPreserving mc s =
    markAndSweepPreserving' (toList (names (known_values s)) `addSearchNames` mc) s

markAndSweepPreserving' :: MemConfig -> State t -> Bindings -> State t
markAndSweepPreserving' PreserveAllMC s _ = s
markAndSweepPreserving' mc (state@State { expr_env = eenv
                                        , type_env = tenv
                                        , curr_expr = cexpr
                                        , path_conds = pc
                                        , exec_stack = es
                                        }) (bindings@Bindings { higher_order_inst = inst }) = -- error $ show $ length $ take 20 $ PC.toList path_conds
                               state'
  where
    state' = state { expr_env = eenv'
                   , type_env = tenv'
                   }

    active = activeNames tenv (E.redirsToExprs eenv) HS.empty $ names cexpr <>
                                                                names es <>
                                                                names pc <>
                                                                names (E.symbolicIds eenv) <>
                                                                S.fromList higher_ord_rel <>
                                                                S.fromList (search_names mc)

    active' = HS.union (pres_func mc state bindings active) active

    isActive :: Name -> Bool
    isActive = (flip HS.member) active'

    eenv' = E.filterWithKey (\n _ -> isActive n) eenv
    tenv' = HM.filterWithKey (\n _ -> isActive n) tenv

    higher_ord_eenv = E.filterWithKey (\n _ -> n `HS.member` inst) eenv
    higher_ord = nubBy (.::.) $ argTypesTEnv tenv ++ E.higherOrderExprs higher_ord_eenv
    higher_ord_rel = E.keys $ E.filter (\e -> any (e .::) higher_ord) higher_ord_eenv

activeNames :: TypeEnv -> ExprEnv -> HS.HashSet Name -> S.Seq Name -> HS.HashSet Name
activeNames tenv eenv explored nss
    | n S.:< ns <- S.viewl nss =
        let
            explored' = HS.insert n explored
            tenv_hits = case HM.lookup n tenv of
                Nothing -> S.empty
                Just r -> names r
            eenv_hits = case E.lookup n eenv of
                Nothing -> S.empty
                Just r -> names r
            ns' = tenv_hits <> eenv_hits <> ns
        in
        if HS.member n explored
          then activeNames tenv eenv explored ns
          else activeNames tenv eenv explored' ns'
    | otherwise = explored
