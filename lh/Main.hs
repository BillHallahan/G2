{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import System.FilePath

import qualified Data.Text as T

import G2.Config
import G2.Interface

import G2.Liquid.Config
import G2.Liquid.Interface

main :: IO ()
main = do
  runSingleLHFun [] []

runSingleLHFun :: [FilePath] -> [FilePath] -> IO ()
runSingleLHFun libs lhlibs = do
  (src, func, config, lhconfig) <- getLHConfig
  let proj = takeDirectory src
  _ <- doTimeout (timeLimit config) $ do
    ((in_out, _), entry) <- findCounterExamples [proj] [src] (T.pack func) libs lhlibs config lhconfig
    printLHOut entry in_out
  return ()