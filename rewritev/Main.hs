{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import DynFlags

import System.Environment
import System.FilePath

import qualified Data.Map as M
import Data.Maybe
import qualified Data.Text as T

import G2.Lib.Printers

import G2.Config
import G2.Interface
import G2.Language
import G2.Translation

import G2.Liquid.Interface
import G2.Equiv.InitRewrite
import G2.Equiv.EquivADT
import G2.Equiv.Verifier

import Control.Exception

import Data.List

import qualified G2.Solver as S
import qualified G2.Language.ExprEnv as E
import qualified G2.Language.PathConds as P
import qualified G2.Language.Naming as N
-- TODO lazy vs. strict
import qualified Data.HashSet as HS

main :: IO ()
main = do
    as <- getArgs

    runWithArgs as

runSingleLHFun :: FilePath -> FilePath -> String -> [FilePath] -> [FilePath] -> [String] -> IO ()
runSingleLHFun proj lhfile lhfun libs lhlibs ars = do
  config <- getConfig ars
  _ <- doTimeout (timeLimit config) $ do
    ((in_out, _), entry) <- findCounterExamples [proj] [lhfile] (T.pack lhfun) libs lhlibs config
    printLHOut entry in_out
  return ()

runWithArgs :: [String] -> IO ()
runWithArgs as = do
  let (src:entry:tail_args) = as

  proj <- guessProj src

  let m_mapsrc = mkMapSrc tail_args

  let tentry = T.pack entry

  config <- getConfig as

  let libs = maybeToList m_mapsrc
  (init_state, bindings) <- initialStateNoStartFunc [proj] [src] libs
                            (TranslationConfig {simpl = True, load_rewrite_rules = True}) config

  let rule = find (\r -> tentry == ru_name r) (rewrite_rules bindings)
  let rule' = case rule of
              Just r -> r
              Nothing -> error "not found"
  res <- checkRule config init_state bindings rule'
  print res
  return ()

checkObligations :: S.Solver solver =>
                    solver ->
                    (State t, State t, HS.HashSet (Expr, Expr)) ->
                    IO (S.Result () ())
checkObligations solver (s1, s2, assumptions) =
    let CurrExpr _ e1 = curr_expr s1
        CurrExpr _ e2 = curr_expr s2
        maybePO = proofObligations s1 s2 e1 e2
    in
    case maybePO of
        Nothing -> error "TODO expressions not equivalent"
        Just po -> let maybeAllPO = obligationWrap po
                       assumptionPC = HS.toList $ HS.map assumptionWrap assumptions
                       newPC = foldr P.insert P.empty (assumptionPC)
                   in
                   case maybeAllPO of
                       Nothing -> applySolver solver newPC s1 s2
                       Just allPO -> applySolver solver (P.insert allPO newPC) s1 s2

applySolver :: S.Solver solver =>
               solver ->
               PathConds ->
               State t ->
               State t ->
               IO (S.Result () ())
applySolver solver extraPC s1 s2 =
    let unionEnv = E.union (expr_env s1) (expr_env s2)
        rightPC = P.toList $ path_conds s2
        unionPC = foldr P.insert (path_conds s1) rightPC
        allPC = foldr P.insert unionPC (P.toList extraPC)
        newState = s1 { expr_env = unionEnv, path_conds = allPC }
    in
    S.check solver newState allPC

assumptionWrap :: (Expr, Expr) -> PathCond
assumptionWrap (e1, e2) =
    -- TODO what type for the equality?
    ExtCond (App (App (Prim Eq TyUnknown) e1) e2) True

obligationWrap :: HS.HashSet (Expr, Expr) -> Maybe PathCond
obligationWrap obligations =
    let obligation_list = HS.toList obligations
        eq_list = map (\(e1, e2) -> App (App (Prim Eq TyUnknown) e1) e2) obligation_list
        conj = foldr1 (\o1 o2 -> App (App (Prim And TyUnknown) o1) o2) eq_list
    in
    if null eq_list
    then Nothing
    else Just $ ExtCond (App (Prim Not TyUnknown) conj) True

mkMapSrc :: [String] -> Maybe String
mkMapSrc a = strArg "mapsrc" a M.empty Just Nothing
