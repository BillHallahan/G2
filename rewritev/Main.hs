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
  (exec_res, bindings') <- runG2WithConfig rewrite_state_r config bindings
  printFuncCalls config (Id (Name tentry Nothing 0 Nothing) TyUnknown)
                 bindings' exec_res
  print "right-hand side end\n"

  let rewrite_state_l = initWithLHS init_state $ rule'
  print "left-hand side start\n"
  (exec_res_l, bindings_l) <- runG2WithConfig rewrite_state_l config bindings
  printFuncCalls config (Id (Name tentry Nothing 0 Nothing) TyUnknown)
                 bindings_l exec_res_l
  print "left-hand side end\n"

  SomeSolver solver <- initSolver config
  let expr_r = curr_expr rewrite_state_r
  let expr_l = curr_expr rewrite_state_l
  let maybePO = proofObligations rewrite_state_l rewrite_state_r expr_l expr_r
  print maybePO

  return ()

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
