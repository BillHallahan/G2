{-# LANGUAGE OverloadedStrings #-}

module Main where

import System.Environment

import Data.List as L
import Data.Maybe
import qualified Data.Text as T

import G2.Lib.Printers

import G2.Internals.Config.Config
import G2.Internals.Execution
import G2.Internals.Interface
import G2.Internals.Language
import G2.Internals.Translation
import G2.Internals.Solver

import G2.Internals.Liquid.Interface

main :: IO ()
main = do
  as <- getArgs
  let (proj:prims:_) = as


  let m_liquid_file = mkLiquid as
  let m_liquid_func = mkLiquidFunc as
  let m_filetest = mkLiquidFileTest as
  let m_dirtest = mkLiquidDirTest as

  let libs = maybeToList $ mkMapSrc as
  let lhlibs = maybeToList $ mkLiquidLibs as

  case m_filetest of
    Just lhfile -> runSingleLHFile proj prims lhfile libs lhlibs as
    Nothing -> case m_dirtest of
      Just dir -> runMultiLHFile proj prims dir libs lhlibs as
      Nothing -> case (m_liquid_file, m_liquid_func) of
        (Just lhfile, Just lhfun) -> runSingleLHFun proj prims lhfile lhfun libs lhlibs as
        _ -> runGHC as

runMultiLHFile :: FilePath -> FilePath -> FilePath -> [FilePath] -> [FilePath] -> [String] -> IO ()
runMultiLHFile proj prim lhdir libs lhlibs args = do
  let config = mkConfig args
  in_out <- testLiquidDir proj prim lhdir libs lhlibs config

  return ()

runSingleLHFile :: FilePath -> FilePath -> FilePath -> [FilePath] -> [FilePath] -> [String] -> IO ()
runSingleLHFile proj prim lhfile libs lhlibs args = do
  let config = mkConfig args
  in_out <- testLiquidFile proj prim lhfile libs lhlibs config
  printParsedLHOut in_out

runSingleLHFun :: FilePath -> FilePath -> FilePath -> String -> [FilePath] -> [FilePath] -> [String] -> IO()
runSingleLHFun proj prim lhfile lhfun libs lhlibs args = do
  let config = mkConfig args
  in_out <- findCounterExamples proj prim lhfile (T.pack lhfun) libs lhlibs config
  printLHOut (T.pack lhfun) in_out

runGHC :: [String] -> IO ()
runGHC as = do
  let (proj:src:base:entry:tail_args) = as

  --Get args
  let m_assume = mAssume tail_args
  let m_assert = mAssert tail_args
  let m_reaches = mReaches tail_args

  let m_mapsrc = mkMapSrc tail_args

  let tentry = T.pack entry

  let libs = maybeToList m_mapsrc

  (mb_modname, pre_binds, pre_tycons, pre_cls) <- translateLoaded proj src base libs True

  let (binds, tycons, cls) = (pre_binds, pre_tycons, pre_cls)
  let init_state = initState binds tycons cls (fmap T.pack m_assume) (fmap T.pack m_assert) (fmap T.pack m_reaches) (isJust m_assert || isJust m_reaches) tentry mb_modname

  -- error $ pprExecStateStr init_state

  let config = mkConfig as

  (con, hhp) <- getSMT config

  in_out <- run stdReduce con hhp config init_state

  -- putStrLn "----------------\n----------------"

  printFuncCalls tentry in_out



printFuncCalls :: T.Text -> [(State t, [Rule], [Expr], Expr, Maybe (Name, [Expr], Expr))] -> IO ()
printFuncCalls entry =
    mapM_ (\(s, _, inArg, ex, ais) -> do
        let funcCall = mkCleanExprHaskell (known_values s) (type_classes s)
                     . foldl (\a a' -> App a a') (Var $ Id (Name entry Nothing 0) TyBottom) $ inArg

        let funcOut = mkCleanExprHaskell (known_values s) (type_classes s) $ ex

        -- print $ model s
        -- print inArg
        -- print ex
        -- print ais

        putStrLn $ funcCall ++ " = " ++ funcOut)

mAssume :: [String] -> Maybe String
mAssume a = mArg "--assume" a Just Nothing

mAssert :: [String] -> Maybe String
mAssert a = mArg "--assert" a Just Nothing

mReaches :: [String] -> Maybe String
mReaches a = mArg "--reaches" a Just Nothing

mWrapper :: [String] -> Maybe String
mWrapper a = mArg "--wrapper" a Just Nothing

mWrapWith :: [String] -> Maybe String
mWrapWith a = mArg "--wrap-with" a Just Nothing

mWrapperInt :: [String] -> Int
mWrapperInt a = mArg "--wrap-i" a read (-1)

mkPolyPred :: [String] -> Maybe String
mkPolyPred a = mArg "--poly-pred" a Just Nothing

mkPolyPredWith :: [String] -> Maybe String
mkPolyPredWith a = mArg "--poly-pred-with" a Just Nothing

mkPolyPredInt :: [String] -> Int
mkPolyPredInt a = mArg "--poly-pred-i" a read (-1)

mkLiquid :: [String] -> Maybe String
mkLiquid a = mArg "--liquid" a Just Nothing

mkLiquidFunc :: [String] -> Maybe String
mkLiquidFunc a = mArg "--liquid-func" a Just Nothing

mkMapSrc :: [String] -> Maybe String
mkMapSrc a = mArg "--mapsrc" a Just Nothing

mkLiquidLibs :: [String] -> Maybe String
mkLiquidLibs a = mArg "--liquid-libs" a Just Nothing

mkLiquidFileTest :: [String] -> Maybe String
mkLiquidFileTest a = mArg "--liquid-file-test" a Just Nothing

mkLiquidDirTest :: [String] -> Maybe String
mkLiquidDirTest a = mArg "--liquid-dir-test" a Just Nothing

