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

mkMapSrc :: [String] -> Maybe String
mkMapSrc a = strArg "mapsrc" a M.empty Just Nothing
