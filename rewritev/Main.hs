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

import ZenoSuite

main :: IO ()
main = do
    as <- getArgs

    if length as == 1 then
        let n = read (head as) :: Int
        in ZenoSuite.suite n
    else
        runWithArgs as

runWithArgs :: [String] -> IO ()
runWithArgs as = do
  let (src:entry:tail_args) = as

  proj <- guessProj src

  -- TODO for now, total as long as there's an extra arg
  -- TODO finite variables
  let total = map T.pack tail_args
      m_mapsrc = mkMapSrc []
      tentry = T.pack entry
      finite = []

  config <- getConfig as

  let libs = maybeToList m_mapsrc
  (init_state, bindings) <- initialStateNoStartFunc [proj] [src] libs
                            (TranslationConfig {simpl = True, load_rewrite_rules = True}) config

  let rule = find (\r -> tentry == ru_name r) (rewrite_rules bindings)
      rule' = case rule of
              Just r -> r
              Nothing -> error "not found"
  res <- checkRule config init_state bindings total finite rule'
  print res
  return ()

mkMapSrc :: [String] -> Maybe String
mkMapSrc a = strArg "mapsrc" a M.empty Just Nothing
