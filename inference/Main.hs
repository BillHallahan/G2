{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import G2.Config as G2
import G2.Interface
import G2.Liquid.Interface
import G2.Liquid.Inference.Config
import G2.Liquid.Inference.G2Calls
import G2.Liquid.Inference.Interface
import G2.Liquid.Inference.QualifGen
import G2.Liquid.Inference.Verify
import G2.Liquid.Types

import Language.Fixpoint.Solver
import Language.Fixpoint.Types.Constraints
import Language.Haskell.Liquid.Types as LH

import Control.DeepSeq
import qualified Data.Map as M
import qualified Data.Text as T
import Data.Time.Clock
import System.Environment

import G2.Language

import Language.Haskell.Liquid.GHC.Interface

main :: IO ()
main = do
    as <- getArgs
    config <- G2.getConfig as
    let infconfig = mkInferenceConfig as

        func = strArg "liquid-func" as M.empty Just Nothing

    case as of
        (f:_) -> 
            case func of
                Nothing -> do
                            if "--qualif" `elem` as
                                then checkQualifs f config
                                else callInference f infconfig config
                Just func -> do
                    ((in_out, _), entry) <- runLHInferenceAll infconfig config (T.pack func) [] [f] []
                    printLHOut entry in_out
                    return ()
        _ -> error "No path given"

checkQualifs :: String -> G2.Config -> IO ()
checkQualifs f config = do
    qualifGen "qualif.hquals" 
    
    finfo <- parseFInfo ["qualif.hquals"]

    let infconfig = mkInferenceConfig []
    lhconfig <- quals finfo `deepseq` defLHConfig [] []
    let lhconfig' = lhconfig { pruneUnsorted = True }
    ghcis <- ghcInfos Nothing lhconfig' [f]
    let ghcis' = map (\ghci ->
                        let
                            spc = spec ghci
                            spc' = spc { gsQualifiers = gsQualifiers spc ++ quals finfo }
                        in
                        ghci { spec = spc' }) ghcis

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
