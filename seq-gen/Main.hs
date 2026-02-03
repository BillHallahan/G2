{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import G2.Config
import G2.SMTSynth.Synthesizer

import Data.List
import qualified Data.Text as T
import System.Directory

main :: IO ()
main = do
    (src, m_entry, config) <- getSeqGenConfig
    let config' = config { favor_chars = True }
    case m_entry of
        Just entry -> do
            let f = T.pack entry
            _ <- genSMTFunc [] [src] f Nothing config'
            return ()
        Nothing -> do
            cnt <- readFile src
            let lns = lines cnt
            mapM_ (run config') $ map T.pack lns
        where
            run con f = do
                let spl_f = T.splitOn "." f
                    dir_name = map T.unpack $ init spl_f
                    f_name = last spl_f
                def <- genSMTFunc [] [] f_name Nothing con
                updateMainSMT $ "SMT":dir_name
                createAppend ("SMT":dir_name) def
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
                        writeFile fle ("{-# LANGUAGE MagicHash #-}\n\n")
                        appendFile fle ("module " ++ mdl ++ " where\n\nimport GHC.Prim2\n\n")
                appendFile fle (def ++ "\n\n")
            
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

