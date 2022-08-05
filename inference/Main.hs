{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import G2.Config as G2
import G2.Interface
import G2.Liquid.Config
import G2.Liquid.Interface
import G2.Liquid.Inference.Config
import G2.Liquid.Inference.G2Calls
import G2.Liquid.Inference.Initalization
import G2.Liquid.Inference.Interface
import G2.Liquid.Inference.Verify
import G2.Liquid.Helpers

import Language.Fixpoint.Solver
import Language.Fixpoint.Types.Constraints
import Language.Haskell.Liquid.Types as LH

import Control.DeepSeq
import qualified Data.Map as M
import qualified Data.Text as T
import Data.Time.Clock
import System.Environment

main :: IO ()
main = do
    (f, count, config, g2lhconfig, infconfig, func) <- getAllConfigsForInf

    case (func) of
        Nothing -> do
                    if count
                            then checkFuncNums f infconfig config g2lhconfig
                            else callInference f infconfig config g2lhconfig
        Just func' -> do
            ((in_out, _), entry) <- runLHInferenceAll infconfig config g2lhconfig (T.pack func') [] [f] []
            printLHOut entry in_out
            return ()

-- checkQualifs :: String -> G2.Config -> IO ()
-- checkQualifs f config = do
--     undefined
--     -- qualifGen "qualif.hquals" 
    
--     finfo <- parseFInfo ["qualif.hquals"]

--     let infconfig = mkInferenceConfig []
--     lhconfig <- quals finfo `deepseq` defLHConfig [] []
--     let lhconfig' = lhconfig { pruneUnsorted = True }
--     ghcis <- ghcInfos Nothing lhconfig' [f]
--     let ghcis' = map (\ghci ->
--                         let
--                             ghci_quals = getQualifiers ghci-- spc = spec ghci
--                             new_quals = ghci_quals ++ quals finfo 
--                         in
--                         putQualifiers ghci new_quals) ghcis

--     start <- getCurrentTime
--     res <- doTimeout 360 $ verify infconfig lhconfig' ghcis'
--     stop <- getCurrentTime

--     case res of -- print $ quals finfo
--         Just Safe -> do
--             putStrLn "Safe"
--             print (stop `diffUTCTime` start)
--         Just _ -> putStrLn "Unsafe"
--         Nothing -> putStrLn "Timeout"

callInference :: String -> InferenceConfig -> G2.Config -> LHConfig -> IO ()
callInference f infconfig config lhconfig = do
    (s, gs) <- inferenceCheck infconfig config lhconfig [] [f] []
    case gs of
        Left gs' -> do
            putStrLn "Counterexample"
            printCE s gs'
        Right gs' -> do
            putStrLn "Safe"
            print gs'

checkFuncNums :: String -> InferenceConfig -> G2.Config -> LHConfig -> IO ()
checkFuncNums f infconfig config g2lhconfig = do
    (ghci, lhconfig) <- getGHCI infconfig [] [f] []
    (lrs, _, _, _, main_mod)  <- getInitState [] [f] [] ghci infconfig config g2lhconfig
    let nls = getNameLevels main_mod lrs

    print nls

    print $ length nls
    print $ length (concat nls) - 1

    return ()
