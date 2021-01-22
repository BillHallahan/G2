{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import DynFlags

import System.Environment
import System.FilePath

import qualified Data.Map as M
import Data.Maybe
import qualified Data.Text as T

import G2.Lib.Printers

import G2.Config
import G2.Interface
import G2.Language
import G2.Translation

import G2.Liquid.Interface
import G2.Equiv.InitRewrite

import Control.Exception

import Data.List

{-
import G2.Config as G2
import G2.Interface
import G2.Liquid.Interface
import G2.Liquid.Inference.Config
import G2.Liquid.Inference.G2Calls
import G2.Liquid.Inference.Interface
import G2.Liquid.Inference.QualifGen
import G2.Liquid.Inference.Verify
import G2.Liquid.Types

-- TODO
--import G2.Translation.Interface

import Language.Fixpoint.Solver
import Language.Fixpoint.Types.Constraints
-- import Language.Haskell.Liquid.Types as LH

import Control.DeepSeq
import qualified Data.Map as M
import qualified Data.Text as T
import Data.Time.Clock
import System.Environment

import G2.Language

import Language.Haskell.Liquid.GHC.Interface
-}

main :: IO ()
main = do
    as <- getArgs
    -- config <- G2.getConfig as
    -- print $ "Yes"

    let m_liquid_file = mkLiquid as
    let m_liquid_func = mkLiquidFunc as

    let libs = maybeToList $ mkMapSrc as
    let lhlibs = maybeToList $ mkLiquidLibs as

    case (m_liquid_file, m_liquid_func) of
        (Just lhfile, Just lhfun) -> do
            let m_idir = mIDir as
                proj = maybe (takeDirectory lhfile) id m_idir
            runSingleLHFun proj lhfile lhfun libs lhlibs as
        _ -> do
            runWithArgs as
    {-
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
    -}

runSingleLHFun :: FilePath -> FilePath -> String -> [FilePath] -> [FilePath] -> [String] -> IO ()
runSingleLHFun proj lhfile lhfun libs lhlibs ars = do
  config <- getConfig ars
  _ <- doTimeout (timeLimit config) $ do
    ((in_out, _), entry) <- findCounterExamples [proj] [lhfile] (T.pack lhfun) libs lhlibs config
    printLHOut entry in_out
  return ()

runWithArgs :: [String] -> IO ()
runWithArgs as = do
  let (src:entry:tail_args) = as

  proj <- guessProj src

  --Get args
  let m_assume = mAssume tail_args
  let m_assert = mAssert tail_args
  let m_reaches = mReaches tail_args
  let m_retsTrue = mReturnsTrue tail_args

  let m_mapsrc = mkMapSrc tail_args

  let tentry = T.pack entry
  -- let tentry = (\_ ng _ _ _ _ -> (Prim Undefined TyBottom, [], [], ng))

  config <- getConfig as

  let libs = maybeToList m_mapsrc
  (init_state, bindings) <- initialStateNoStartFunc [proj] [src] libs
                            (TranslationConfig {simpl = True, load_rewrite_rules = True}) config
  -- (exec_res, bindings') <- runG2WithConfig init_state config bindings

  -- let exprs = map (curr_expr . final_state) exec_res
  -- mapM_ print exprs
  -- mapM_ print (rewrite_rules bindings)
  -- mapM_ (print . curr_expr . initWithRHS init_state) (rewrite_rules bindings)
  let rule = find (\r -> tentry == ru_name r) (rewrite_rules bindings)
  let rule' = case rule of
              Just r -> r
              Nothing -> error "not found"
  -- print . curr_expr . initWithRHS init_state $ rule'
  let rewrite_state_r = initWithRHS init_state $ rule'

  print $ ru_rhs rule'
  print $ ru_bndrs rule'
  
  (exec_res, bindings') <- runG2WithConfig rewrite_state_r config bindings
  printFuncCalls config (Id (Name tentry Nothing 0 Nothing) TyUnknown)
                 bindings' exec_res

  let rewrite_state_l = initWithLHS init_state $ rule'
  (exec_res_l, bindings_l) <- runG2WithConfig rewrite_state_l config bindings
  printFuncCalls config (Id (Name tentry Nothing 0 Nothing) TyUnknown)
                 bindings_l exec_res_l

  {-
  config <- getConfig as
  _ <- doTimeout (timeLimit config) $ do
    ((in_out, b), entry_f@(Id (Name _ mb_modname _ _) _)) <-
        runG2FromFile [proj] [src] libs (fmap T.pack m_assume)
                  (fmap T.pack m_assert) (fmap T.pack m_reaches) 
                  (isJust m_assert || isJust m_reaches || m_retsTrue) 
                  tentry (TranslationConfig {simpl = True, load_rewrite_rules = True}) config

    case validate config of
        True -> do
            r <- validateStates [proj] [src] (T.unpack $ fromJust mb_modname) entry [] [Opt_Hpc] in_out
            if r then putStrLn "Validated" else putStrLn "There was an error during validation."

            -- runHPC src (T.unpack $ fromJust mb_modname) entry in_out
        False -> return ()

    printFuncCalls config entry_f b in_out
  -}

  return ()

printFuncCalls :: Config -> Id -> Bindings -> [ExecRes t] -> IO ()
printFuncCalls config entry b =
    mapM_ (\execr@(ExecRes { final_state = s}) -> do
        let funcCall = mkCleanExprHaskell s
                     . foldl (\a a' -> App a a') (Var entry) $ (conc_args execr)

        let funcOut = mkCleanExprHaskell s $ (conc_out execr)

        ppStatePiece (printExprEnv config)  "expr_env" $ ppExprEnv s
        ppStatePiece (printRelExprEnv config) "rel expr_env" $ ppRelExprEnv s b
        ppStatePiece (printCurrExpr config) "curr_expr" $ ppCurrExpr s
        ppStatePiece (printPathCons config) "path_cons" $ ppPathConds s

        putStrLn $ funcCall ++ " = " ++ funcOut)

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

mkMapSrc :: [String] -> Maybe String
mkMapSrc a = strArg "mapsrc" a M.empty Just Nothing

mkLiquidLibs :: [String] -> Maybe String
mkLiquidLibs a = strArg "liquid-libs" a M.empty Just Nothing

{-
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
-}
