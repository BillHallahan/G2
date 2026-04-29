{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import G2.Config.Config
import G2.Interface.Interface
import G2.SMTSynth.Synthesizer

import Data.List
import Data.Maybe
import qualified Data.Text as T
import System.Directory

main :: IO ()
main = do
    sc@(SynthConfig {run_file = src, synth_func = m_entry, synth_all_list = m_list, run_symex = run_sym }) <- getSeqGenConfig
    case (m_entry, m_list) of
        (Just entry, _) -> do
            let f = T.pack entry
            _ <- case run_sym of
                        False -> do _ <- genSMTFunc [] [src] f Nothing sc; return ()
                        True -> do _ <- runFunc src [] f Nothing sc; return ()
            return ()
        (_, Just file_list) -> do
            cnt <- readFile file_list
            let lns = lines cnt
            mapM_ (run src sc) $ map T.pack lns
        _ -> error "Must pass a function to run or a file with a list of functions"
        where
            run src sc@(SynthConfig { g2_config = con }) gen_f = do
                let (f, gen_for_ty) = T.break (== ';') gen_f
                    gen_for_ty' = T.unpack $ T.tail gen_for_ty
                    spl_f = T.splitOn "." f
                    dir_name = map T.unpack $ init spl_f
                    f_name = last spl_f

                    con' = setSynthMode (fromMaybe (error $ "error: " ++ gen_for_ty' ++ " not recognized")
                                      $ lookup gen_for_ty' synthModeMapping) con

                m_ty_def <- doTimeout 60 $ genSMTFunc [] [src] f Nothing $ sc { g2_config = con' }
                case m_ty_def of
                    Just (ty, def) -> do
                        updateMainSMT $ "SMT":gen_for_ty':dir_name
                        createAppend ("SMT":gen_for_ty':dir_name) $ (T.unpack . smtNameWrap . smtName $ f_name) ++ " :: " ++ ty
                        createAppend ("SMT":gen_for_ty':dir_name) def
                        createAppend ("SMT":gen_for_ty':dir_name) "\n"
                    Nothing -> return ()
            
            createAppend path def = do
                let dir = "smt/" ++ intercalate "/" (init path)
                    fle = dir ++ "/" ++ last path ++ ".hs"
                    mdl = intercalate "." path
                exists <- doesFileExist fle
                case exists of
                    True -> return ()
                    False -> do
                        createDirectoryIfMissing True dir
                        writeFile fle ("{-# LANGUAGE BangPatterns, MagicHash, RankNTypes, ViewPatterns #-}\n\n")
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

