{-# LANGUAGE MultiWayIf #-}
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
import G2.Equiv.Summary
import G2.Equiv.Verifier

import Control.Exception

import Data.List
import Data.Char

import ZenoSuite

main :: IO ()
main = do
    as <- getArgs

    if length as == 1 then
        let n = read (head as) :: Int
        in ZenoSuite.suite n
    else
        runWithArgs as

finiteArg :: String -> Bool
finiteArg ('_':_) = True
finiteArg _ = False

isFlagOrNumber :: String -> Bool
isFlagOrNumber ('-':'-':_) = True
isFlagOrNumber (c:_) = isDigit c
isFlagOrNumber _ = False

runWithArgs :: [String] -> IO ()
runWithArgs as = do
  let (src:entry:tail_args) = as
      (flags_nums, tail_vars) = partition isFlagOrNumber tail_args
      sync = "--constant-sync" `elem` flags_nums
      print_summary = if | "--summarize" `elem` flags_nums -> NoHistory
                         | "--hist-summarize" `elem` flags_nums -> WithHistory
                         | otherwise -> NoSummary
      limit = case elemIndex "--limit" tail_args of
        Nothing -> -1
        Just n -> read (tail_args !! (n + 1)) :: Int

  proj <- guessProj src

  -- TODO for now, total as long as there's an extra arg
  -- TODO finite variables
  let (finite_names, total_names) = partition finiteArg tail_vars
      finite = map (T.pack . tail) finite_names
      -- TODO don't need to add finite to this
      total = (map T.pack total_names) ++ finite
      m_mapsrc = mkMapSrc []
      tentry = T.pack entry

  config <- getConfig as

  let libs = maybeToList m_mapsrc
  (init_state, bindings) <- initialStateNoStartFunc [proj] [src] libs
                            (TranslationConfig {simpl = True, load_rewrite_rules = True}) config

  let rule = find (\r -> tentry == ru_name r) (rewrite_rules bindings)
      rule' = case rule of
              Just r -> r
              Nothing -> error "not found"
  res <- checkRule config sync init_state bindings total finite print_summary limit rule'
  print res
  return ()

mkMapSrc :: [String] -> Maybe String
mkMapSrc a = strArg "mapsrc" a M.empty Just Nothing
