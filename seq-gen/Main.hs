{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import G2.Config
import G2.SMTSynth.Synthesizer

import Data.List
import Data.Maybe
import qualified Data.Text as T
import System.Directory

main :: IO ()
main = do
    SynthConfig {run_file = src, synth_func = m_entry, run_symex = run_sym, g2_config = config} <- getSeqGenConfig
    case m_entry of
        Just entry -> do
            let f = T.pack entry
            _ <- case run_sym of
                        False -> do genSMTFunc [] [src] f Nothing config; return ()
                        True -> do runFunc src [] f Nothing config; return ()
            return ()
        Nothing -> do
            cnt <- readFile src
            let lns = lines cnt
            mapM_ (run config) $ map T.pack lns
        where
            run con gen_f = do
                let (f, gen_for_ty) = T.break (== ';') gen_f
                    gen_for_ty' = T.unpack $ T.tail gen_for_ty
                    spl_f = T.splitOn "." f
                    dir_name = map T.unpack $ init spl_f
                    f_name = last spl_f

                    con' = setSynthMode (fromMaybe (error $ "error: " ++ gen_for_ty' ++ " not recognized")
                                      $ lookup gen_for_ty' synthModeMapping) con

                (ty, def) <- genSMTFunc [] [] f Nothing con'
                updateMainSMT $ "SMT":gen_for_ty':dir_name
                createAppend ("SMT":gen_for_ty':dir_name) $ (T.unpack . smtNameWrap . smtName $ f_name) ++ " :: " ++ ty
                createAppend ("SMT":gen_for_ty':dir_name) def
                createAppend ("SMT":gen_for_ty':dir_name) "\n"
                return ()
            
            createAppend path def = do
                let dir = "smt/" ++ intercalate "/" (init path)
                    fle = dir ++ "/" ++ last path ++ ".hs"
                    mdl = intercalate "." path
                exists <- doesFileExist fle
                case exists of
                    True -> return ()
                    False -> do
                        createDirectoryIfMissing True dir
                        writeFile fle ("{-# LANGUAGE MagicHash, ViewPatterns #-}\n\n")
                        appendFile fle ("module " ++ mdl ++ " where\n\nimport GHC.Prim2\n\n")
                appendFile fle (def ++ "\n")
            
            updateMainSMT path = do
                let smt_file = "smt/SMT.hs" 
                    mdl = intercalate "." path
                exists <- doesFileExist smt_file
                case exists of
                    True -> return ()
                    False -> do
                        createDirectoryIfMissing True "smt"
                        writeFile smt_file ("module SMT where\n\n")
                r <- readFile smt_file
                case ("import " ++ mdl) `isInfixOf` r of
                    True -> return ()
                    False -> appendFile smt_file ("import " ++ mdl ++ "\n\n")

