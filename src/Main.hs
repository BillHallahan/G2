{-# LANGUAGE OverloadedStrings #-}

module Main where

import System.Environment
import System.Timeout

import Data.List as L
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Text as T

import G2.Lib.Printers

import G2.Internals.Config.Config
import G2.Internals.Config.Interface
import G2.Internals.Execution
import G2.Internals.Interface
import G2.Internals.Language
import G2.Internals.Language.ExprEnv (EnvObj(..))
import G2.Internals.Translation
import G2.Internals.Solver

import G2.Internals.Liquid.Interface

_DEFAULT_TIMEOUT = 120 * 1000 * 1000 -- microseconds = 10^-6 seconds

main :: IO ()
main = do
  as <- getArgs
  let (proj:_) = as

  let m_liquid_file = mkLiquid as
  let m_liquid_func = mkLiquidFunc as
  let m_filetest = mkLiquidFileTest as
  let m_dirtest = mkLiquidDirTest as

  let libs = maybeToList $ mkMapSrc as
  let lhlibs = maybeToList $ mkLiquidLibs as

  case m_filetest of
    Just lhfile -> do
      doTimeout _DEFAULT_TIMEOUT $ runSingleLHFile proj lhfile libs lhlibs as
      return ()
    Nothing -> case m_dirtest of
      Just dir -> runMultiLHFile proj dir libs lhlibs as
      Nothing -> case (m_liquid_file, m_liquid_func) of
        (Just lhfile, Just lhfun) -> do
          doTimeout _DEFAULT_TIMEOUT $ runSingleLHFun proj lhfile lhfun libs lhlibs as
          return ()
        _ -> do
          doTimeout _DEFAULT_TIMEOUT $ runGHC as
          return ()

doTimeout :: Int -> IO a -> IO ()
doTimeout micros action = do
  res <- timeout micros action
  case res of
    Just _ -> return ()
    Nothing -> do
      putStrLn "Timeout!"
      return ()

runMultiLHFile :: FilePath -> FilePath -> [FilePath] -> [FilePath] -> [String] -> IO ()
runMultiLHFile proj lhdir libs lhlibs args = do
  config <- getConfig args
  in_out <- testLiquidDir proj lhdir libs lhlibs config

  return ()

runSingleLHFile :: FilePath -> FilePath -> [FilePath] -> [FilePath] -> [String] -> IO ()
runSingleLHFile proj lhfile libs lhlibs args = do
  config <- getConfig args
  in_out <- testLiquidFile proj lhfile libs lhlibs config
  printParsedLHOut in_out

runSingleLHFun :: FilePath -> FilePath -> String -> [FilePath] -> [FilePath] -> [String] -> IO()
runSingleLHFun proj lhfile lhfun libs lhlibs args = do
  config <- getConfig args
  in_out <- findCounterExamples proj lhfile (T.pack lhfun) libs lhlibs config
  printLHOut (T.pack lhfun) in_out

runGHC :: [String] -> IO ()
runGHC as = do

  let (proj:src:entry:tail_args) = as

  --Get args
  let m_assume = mAssume tail_args
  let m_assert = mAssert tail_args
  let m_reaches = mReaches tail_args

  let m_mapsrc = mkMapSrc tail_args

  let tentry = T.pack entry

  let libs = maybeToList m_mapsrc

  config <- getConfig as

  (mb_modname, pre_binds, pre_tycons, pre_cls,_) <- translateLoaded proj src libs True config

  let (binds, tycons, cls) = (pre_binds, pre_tycons, pre_cls)
  let init_state = initState binds tycons cls (fmap T.pack m_assume) (fmap T.pack m_assert) (fmap T.pack m_reaches) (isJust m_assert || isJust m_reaches) tentry mb_modname
  let halter_set_state = init_state {halter = steps config}

  -- error $ pprExecStateStr init_state

  (con, hhp) <- getSMT config

  in_out <- run stdReduce halterIsZero halterSub1 executeNext con hhp config halter_set_state

  -- putStrLn "----------------\n----------------"

  printFuncCalls tentry in_out



printFuncCalls :: T.Text -> [(State h t, [Expr], Expr, Maybe FuncCall)] -> IO ()
printFuncCalls entry =
    mapM_ (\(s, inArg, ex, ais) -> do
        let funcCall = mkCleanExprHaskell (known_values s) (type_classes s)
                     . foldl (\a a' -> App a a') (Var $ Id (Name entry Nothing 0) TyBottom) $ inArg

        let funcOut = mkCleanExprHaskell (known_values s) (type_classes s) $ ex

        -- print $ model s
        -- print inArg
        -- print ex
        -- print ais

        putStrLn $ funcCall ++ " = " ++ funcOut)

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

mkLiquidFileTest :: [String] -> Maybe String
mkLiquidFileTest a = strArg "liquid-file-test" a M.empty Just Nothing

mkLiquidDirTest :: [String] -> Maybe String
mkLiquidDirTest a = strArg "liquid-dir-test" a M.empty Just Nothing

