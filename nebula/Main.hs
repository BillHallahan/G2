{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as T

import G2.Config
import G2.Interface
import G2.Language
import G2.Translation

import G2.Equiv.Config
import G2.Equiv.Verifier

import Data.List

main :: IO ()
main = do
  (src, entry, total, nebula_config) <- getNebulaConfig

  config <- getConfigDirect

  proj <- guessProj (includePaths config) src

  let tentry = T.pack entry

  (init_state, bindings, _) <- initialStateNoStartFunc proj [src]
                               (simplTranslationConfig { simpl = True, load_rewrite_rules = True, hpc_ticks = False }) config

  let rule = find (\r -> tentry == ru_name r) (rewrite_rules bindings)
      rule' = case rule of
              Just r -> r
              Nothing -> error "not found"
  res <- checkRule config nebula_config init_state bindings total rule'
  print res
  return ()
