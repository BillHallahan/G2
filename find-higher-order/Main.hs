{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as T

import G2.Config
import G2.Interface
import qualified G2.Initialization.Types as IT
import G2.Language
import qualified G2.Language.ExprEnv as E
import qualified G2.Language.TyVarEnv as TV
import G2.Translation

import G2.Equiv.Config
import G2.Equiv.Verifier

import Data.List
import qualified Data.Text as T
import System.Environment

main :: IO ()
main = do
  src:_ <- getArgs

  config <- getConfigDirect

  proj <- guessProj (includePaths config) src

  (init_state, bindings, mods) <- initialStateNoStartFunc
                                        proj [src]
                                        (simplTranslationConfig { hpc_ticks = False })
                                        config

  let rel_eenv = E.filterWithKey (\(Name _ m _ _) _ -> m `elem` mods) $ expr_env init_state
  let rel_funcs_eenv = E.filter isHigherOrderFunc rel_eenv
  let rel_funcs = map formatName $ E.keys rel_funcs_eenv

  putStrLn . T.unpack $ T.intercalate "\n" rel_funcs

  return ()

isHigherOrderFunc :: Expr -> Bool
isHigherOrderFunc = not . null . higherOrderFuncs . typeOf TV.empty

formatName :: Name -> T.Text
formatName (Name n Nothing _ _) = n
formatName (Name n (Just m) _ _) = m <> "." <> n