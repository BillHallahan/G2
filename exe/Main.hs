{-# LANGUAGE FlexibleContexts, OverloadedStrings #-}

module Main (main) where

import G2.Translation.GHC (GeneralFlag(Opt_Hpc))

import System.Environment
import System.FilePath

import Control.Monad
import Data.Foldable (toList)
import qualified Data.List as L
import qualified Data.Map as M
import Data.Maybe
import Data.Monoid ((<>))
import qualified Data.Sequence as S
import qualified Data.Text as T
import qualified Data.Text.IO as T

import G2.Lib.Printers

import G2.Config
import G2.Interface
import G2.Language
import G2.Translation

main :: IO ()
main = do
  as <- getArgs
  runWithArgs as

runWithArgs :: [String] -> IO ()
runWithArgs as = do
  let (_:_:tail_args) = as
  (src, entry, m_assume, m_assert, config) <- getConfig

  proj <- guessProj (includePaths config) src

  --Get args
  let m_reaches = mReaches tail_args
  let m_retsTrue = mReturnsTrue tail_args

  let gFlags = if measure_coverage config then [Opt_Hpc] else []

  (in_out, b, _, entry_f@(Id (Name _ mb_modname _ _) _)) <-
        runG2FromFile proj [src] gFlags (fmap T.pack m_assume)
                  (fmap T.pack m_assert) (fmap T.pack m_reaches) 
                  (isJust m_assert || isJust m_reaches || m_retsTrue) 
                  entry simplTranslationConfig config

  let (unspecified_output, spec_output) = L.partition (\ExecRes { final_state = s } -> getExpr s == Prim UnspecifiedOutput TyBottom) in_out
  
  let notValidated = filter (\res@ExecRes{validated = val} -> case val of
                                                                    Just m -> m == False
                                                                    Nothing -> False ) in_out
  when (validate config) $ do
    if null notValidated then putStrLn "All states are validated" else putStrLn "One or more validation failed"
    
  when (print_num_post_call_func_arg config) $ do
        putStrLn $ "Post call states: " ++ show (length spec_output)
        putStrLn $ "Func arg states: " ++ show (length unspecified_output)

  when (measure_coverage config) $
    runHPC src (T.unpack $ fromJust mb_modname) entry (filter (\x@ExecRes{validated = val} -> fromMaybe False val) in_out)

mReturnsTrue :: [String] -> Bool
mReturnsTrue a = boolArg "returns-true" a M.empty Off

mReaches :: [String] -> Maybe String
mReaches a = strArg "reaches" a M.empty Just Nothing