{-# LANGUAGE OverloadedStrings #-}

module Main (main, plugin) where

import DynFlags

import System.Environment

import qualified Data.Map as M
import Data.Maybe
import qualified Data.Text as T

import G2.Lib.Printers

import G2.Config
import G2.Interface
import G2.Language
import G2.Translation

import G2.Liquid.Interface

import G2.Plugin

main :: IO ()
main = do
  as <- getArgs
  let (proj:_) = as

  let m_liquid_file = mkLiquid as
  let m_liquid_func = mkLiquidFunc as

  let libs = maybeToList $ mkMapSrc as
  let lhlibs = maybeToList $ mkLiquidLibs as

  case (m_liquid_file, m_liquid_func) of
      (Just lhfile, Just lhfun) -> do
        runSingleLHFun proj lhfile lhfun libs lhlibs as
      _ -> do
        runWithArgs as

runSingleLHFun :: FilePath -> FilePath -> String -> [FilePath] -> [FilePath] -> [String] -> IO ()
runSingleLHFun proj lhfile lhfun libs lhlibs ars = do
  config <- getConfig ars
  _ <- doTimeout (timeLimit config) $ do
    (in_out, entry) <- findCounterExamples proj lhfile (T.pack lhfun) libs lhlibs config
    printLHOut entry in_out
  return ()

runWithArgs :: [String] -> IO ()
runWithArgs as = do

  let (proj:src:entry:tail_args) = as

  --Get args
  let m_assume = mAssume tail_args
  let m_assert = mAssert tail_args
  let m_reaches = mReaches tail_args
  let m_retsTrue = mReturnsTrue tail_args

  let m_mapsrc = mkMapSrc tail_args

  let tentry = T.pack entry

  let libs = maybeToList m_mapsrc

  config <- getConfig as
  _ <- doTimeout (timeLimit config) $ do
    (in_out, entry_f@(Id (Name _ mb_modname _ _) _)) <-
        runG2FromFile proj src libs (fmap T.pack m_assume)
                  (fmap T.pack m_assert) (fmap T.pack m_reaches) 
                  (isJust m_assert || isJust m_reaches || m_retsTrue) 
                  tentry config
    -- (mb_modname, binds, tycons, cls, ex) <- translateLoaded proj src libs True config

    -- let (init_state, entry_f) = initState binds tycons cls (fmap T.pack m_assume) (fmap T.pack m_assert) (fmap T.pack m_reaches) 
    --                            (isJust m_assert || isJust m_reaches || m_retsTrue) tentry mb_modname ex config

    -- in_out <- runG2WithConfig init_state config

    case validate config of
        True -> do
            r <- validateStates proj src (T.unpack $ fromJust mb_modname) entry [] [Opt_Hpc] in_out
            if r then putStrLn "Validated" else putStrLn "There was an error during validation."

            -- runHPC src (T.unpack $ fromJust mb_modname) entry in_out
        False -> return ()

    printFuncCalls config entry_f in_out

  return ()

printFuncCalls :: Config -> Id -> [ExecRes t] -> IO ()
printFuncCalls config entry =
    mapM_ (\execr@(ExecRes { final_state = s }) -> do
        let funcCall = mkCleanExprHaskell s
                     . foldl (\a a' -> App a a') (Var entry) $ (conc_args execr)

        let funcOut = mkCleanExprHaskell s $ (conc_out execr)

        ppStatePiece (printExprEnv config)  "expr_env" $ ppExprEnv s
        ppStatePiece (printRelExprEnv config) "rel expr_env" $ ppRelExprEnv s
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
