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

import Control.Exception

import Data.List

-- TODO new import for solver
import qualified G2.Solver as S
import qualified G2.Language.ExprEnv as E
import qualified G2.Language.PathConds as P
-- TODO lazy vs. strict
import qualified Data.HashSet as HS

main :: IO ()
main = do
    as <- getArgs

    let m_liquid_file = mkLiquid as
    let m_liquid_func = mkLiquidFunc as

    let libs = maybeToList $ mkMapSrc as
    let lhlibs = maybeToList $ mkLiquidLibs as

    case (m_liquid_file, m_liquid_func) of
        (Just lhfile, Just lhfun) -> do
            let m_idir = mIDir as
                proj = maybe (takeDirectory lhfile) id m_idir
            runSingleLHFun proj lhfile lhfun libs lhlibs as
        _ -> do
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

  --Get args
  let m_assume = mAssume tail_args
  let m_assert = mAssert tail_args
  let m_reaches = mReaches tail_args
  let m_retsTrue = mReturnsTrue tail_args

  let m_mapsrc = mkMapSrc tail_args

  let tentry = T.pack entry
  -- let tentry = (\_ ng _ _ _ _ -> (Prim Undefined TyBottom, [], [], ng))

  config <- getConfig as

  let libs = maybeToList m_mapsrc
  (init_state, bindings) <- initialStateNoStartFunc [proj] [src] libs
                            (TranslationConfig {simpl = True, load_rewrite_rules = True}) config
  -- (exec_res, bindings') <- runG2WithConfig init_state config bindings

  -- let exprs = map (curr_expr . final_state) exec_res
  -- mapM_ print exprs
  -- mapM_ print (rewrite_rules bindings)
  -- mapM_ (print . curr_expr . initWithRHS init_state) (rewrite_rules bindings)
  let rule = find (\r -> tentry == ru_name r) (rewrite_rules bindings)
  let rule' = case rule of
              Just r -> r
              Nothing -> error "not found"
  -- print . curr_expr . initWithRHS init_state $ rule'
  let rewrite_state_r = initWithRHS init_state $ rule'

  print $ ru_rhs rule'
  print $ ru_bndrs rule'
  
  print "right-hand side start\n"
  (exec_res_r, bindings') <- runG2WithConfig rewrite_state_r config bindings
  printFuncCalls config (Id (Name tentry Nothing 0 Nothing) TyUnknown)
                 bindings' exec_res_r
  print "right-hand side end\n"

  let rewrite_state_l = initWithLHS init_state $ rule'
  print "left-hand side start\n"
  (exec_res_l, bindings_l) <- runG2WithConfig rewrite_state_l config bindings
  printFuncCalls config (Id (Name tentry Nothing 0 Nothing) TyUnknown)
                 bindings_l exec_res_l
  print "left-hand side end\n"

  let pairs_l = symbolic_ids rewrite_state_l
  let pairs_r = symbolic_ids rewrite_state_r
  let final_states_l = map final_state exec_res_l
  let final_states_r = map final_state exec_res_r
  let pairings = statePairing final_states_l final_states_r $ zip pairs_l pairs_r

  S.SomeSolver solver <- initSolver config
  res <- mapM (checkObligations solver) pairings
  {-
  let CurrExpr _ expr_r = curr_expr rewrite_state_r
  let CurrExpr _ expr_l = curr_expr rewrite_state_l
  let maybePO = proofObligations rewrite_state_l rewrite_state_r expr_l expr_r
  -}
  -- TODO remove print statement
  -- TODO use toList on the HashSet to get the contents
  -- TODO take one of the starting states
  -- union of the expression environments of both
  -- TODO also need path conds union
  -- print maybePO
  {-
  res <- case maybePO of
           Nothing -> error "TODO expressions not equivalent"
           Just po -> let allPC = foldr P.insert P.empty poList
                      in
                      applySolver solver extraPC rewrite_state_l rewrite_state_r
  -}
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
        -- pcList = map extWrap $ HS.toList extraPC
        allPC = foldr P.insert unionPC (P.toList extraPC)
        newState = s1 { expr_env = unionEnv, path_conds = allPC }
    in
    S.check solver newState allPC

printFuncCalls :: Config -> Id -> Bindings -> [ExecRes t] -> IO ()
printFuncCalls config entry b =
    mapM_ (\execr@(ExecRes { final_state = s}) -> do
        let funcCall = mkCleanExprHaskell s
                     . foldl (\a a' -> App a a') (Var entry) $ (conc_args execr)

        let funcOut = mkCleanExprHaskell s $ (conc_out execr)

        ppStatePiece (printExprEnv config)  "expr_env" $ ppExprEnv s
        ppStatePiece (printRelExprEnv config) "rel expr_env" $ ppRelExprEnv s b
        ppStatePiece (printCurrExpr config) "curr_expr" $ ppCurrExpr s
        ppStatePiece (printPathCons config) "path_cons" $ ppPathConds s

        putStrLn $ funcCall ++ " = " ++ funcOut)

assumptionWrap :: (Expr, Expr) -> PathCond
assumptionWrap (e1, e2) =
    -- TODO what type for the equality?
    ExtCond (App (App (Prim Eq TyUnknown) e1) e2) True

obligationWrap :: HS.HashSet (Expr, Expr) -> Maybe PathCond
obligationWrap obligations =
    let obligation_list = HS.toList obligations
        eq_list = map (\(e1, e2) -> App (App (Prim Eq TyUnknown) e1) e2) obligation_list
        -- TODO type issue again
        conj = foldr1 (\o1 o2 -> App (App (Prim And TyUnknown) o1) o2) eq_list
    in
    if null eq_list
    then Nothing
    else Just $ ExtCond (App (Prim Not TyUnknown) conj) True

ppStatePiece :: Bool -> String -> String -> IO ()
ppStatePiece b n res =
    case b of
        True -> do
            putStrLn $ "---" ++ n ++ "---"
            putStrLn res
            putStrLn ""
        False -> return ()

mIDir :: [String] -> Maybe String
mIDir a = strArg "idir" a M.empty Just Nothing

mReturnsTrue :: [String] -> Bool
mReturnsTrue a = boolArg "returns-true" a M.empty Off

mAssume :: [String] -> Maybe String
mAssume a = strArg "assume" a M.empty Just Nothing

mAssert :: [String] -> Maybe String
mAssert a = strArg "assert" a M.empty Just Nothing

mReaches :: [String] -> Maybe String
mReaches a = strArg "reaches" a M.empty Just Nothing

mkLiquid :: [String] -> Maybe String
mkLiquid a = strArg "liquid" a M.empty Just Nothing

mkLiquidFunc :: [String] -> Maybe String
mkLiquidFunc a = strArg "liquid-func" a M.empty Just Nothing

mkMapSrc :: [String] -> Maybe String
mkMapSrc a = strArg "mapsrc" a M.empty Just Nothing

mkLiquidLibs :: [String] -> Maybe String
mkLiquidLibs a = strArg "liquid-libs" a M.empty Just Nothing
