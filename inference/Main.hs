{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import G2.Config as G2
import G2.Interface
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
    as <- getArgs
    config <- G2.getConfig as
    let infconfig = mkInferenceConfig as

        func = strArg "liquid-func" as M.empty Just Nothing
        verif_func = strArg "liquid-verify" as M.empty Just Nothing

    case as of
        (f:_) -> 
            case (func, verif_func) of
                (Nothing, Nothing) -> do
                            if "--qualif" `elem` as
                                then checkQualifs f config
                                else if "--count" `elem` as
                                    then checkFuncNums f infconfig config
                                    else callInference f infconfig config
                (Just func', _) -> do
                    ((in_out, _), entry) <- runLHInferenceAll infconfig config (T.pack func') [] [f] []
                    printLHOut entry in_out
                    return ()
                (_, Just _) -> do
                    (ghci, lhconfig) <- getGHCI infconfig [] [f] []
                    let c = Configs { g2_config = config, lh_config = lhconfig, inf_config = infconfig}
                    r <- runConfigs (tryToVerify ghci) c
                    print r
        _ -> error "No path given"

checkQualifs :: String -> G2.Config -> IO ()
checkQualifs f config = do
    undefined
    -- qualifGen "qualif.hquals" 
    
    finfo <- parseFInfo ["qualif.hquals"]

    let infconfig = mkInferenceConfig []
    lhconfig <- quals finfo `deepseq` defLHConfig [] []
    let lhconfig' = lhconfig { pruneUnsorted = True }
    ghcis <- ghcInfos Nothing lhconfig' [f]
    let ghcis' = map (\ghci ->
                        let
                            ghci_quals = getQualifiers ghci-- spc = spec ghci
                            new_quals = ghci_quals ++ quals finfo 
                        in
                        putQualifiers ghci new_quals) ghcis

    start <- getCurrentTime
    res <- doTimeout 360 $ verify infconfig lhconfig' ghcis'
    stop <- getCurrentTime

    case res of -- print $ quals finfo
        Just Safe -> do
            putStrLn "Safe"
            print (stop `diffUTCTime` start)
        Just _ -> putStrLn "Unsafe"
        Nothing -> putStrLn "Timeout"

callInference :: String -> InferenceConfig -> G2.Config -> IO ()
callInference f infconfig config = do
    gs <- inferenceCheck infconfig config [] [f] []
    case gs of
        Left gs' -> do
            putStrLn "Counterexample"
            print gs'
        Right gs' -> do
            putStrLn "Safe"
            print gs'

checkFuncNums :: String -> InferenceConfig -> G2.Config -> IO ()
checkFuncNums f infconfig config = do
    (ghci, lhconfig) <- getGHCI infconfig [] [f] []
    (lrs, _, _, main_mod)  <- getInitState [] [f] [] ghci infconfig config
    let nls = getNameLevels main_mod lrs

    print nls

    print $ length nls
    print $ length (concat nls) - 1

    return ()
