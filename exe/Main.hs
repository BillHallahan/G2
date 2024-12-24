{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import G2.Translation.GHC (GeneralFlag(Opt_Hpc))

import System.Environment
import System.FilePath

import Data.Foldable (toList)
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

  let tentry = T.pack entry

  _ <- doTimeout (timeLimit config) $ do
    ((in_out, b), entry_f@(Id (Name _ mb_modname _ _) _)) <-
        runG2FromFile proj [src] (fmap T.pack m_assume)
                  (fmap T.pack m_assert) (fmap T.pack m_reaches) 
                  (isJust m_assert || isJust m_reaches || m_retsTrue) 
                  tentry simplTranslationConfig config

    case validate config of
        True -> do
            r <- validateStates proj [src] (T.unpack $ fromJust mb_modname) entry [] [Opt_Hpc] b in_out
            if r then putStrLn "Validated" else putStrLn "There was an error during validation."

            -- runHPC src (T.unpack $ fromJust mb_modname) entry in_out
        False -> return ()

    printFuncCalls config entry_f b in_out

  return ()

printFuncCalls :: Config -> Id -> Bindings -> [ExecRes t] -> IO ()
printFuncCalls config entry b =
    mapM_ (\execr@(ExecRes { final_state = s }) -> do
        let pg = mkPrettyGuide (exprNames $ conc_args execr)
        let (mvp, inp, outp, handles) = printInputOutput pg entry b execr
            sym_gen_out = fmap (printHaskellPG pg s) $ conc_sym_gens execr

        case sym_gen_out of
            S.Empty -> T.putStrLn $ mvp <> inp <> " = " <> outp
            _ -> T.putStrLn $ mvp <> inp <> " = " <> outp <> "\t| generated: " <> T.intercalate ", " (toList sym_gen_out)
        if handles /= "" then T.putStrLn handles else return ())

ppStatePiece :: Bool -> String -> String -> IO ()
ppStatePiece b n res =
    case b of
        True -> do
            putStrLn $ "---" ++ n ++ "---"
            putStrLn res
            putStrLn ""
        False -> return ()

mIDir :: [String] -> Maybe String
mIDir a = strArg "idir" a M.empty Just Nothing

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
