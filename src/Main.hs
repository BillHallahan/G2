{-# LANGUAGE OverloadedStrings #-}

module Main where

import System.Environment

import Data.List as L
import Data.Maybe
import qualified Data.Text as T

import G2.Lib.Printers

import G2.Internals.Config.Config
import G2.Internals.Execution
import G2.Internals.Interface
import G2.Internals.Language
import G2.Internals.Translation
import G2.Internals.Solver

import G2.Internals.Liquid.Interface

main :: IO ()
main = do
    -- timedMsg "G2 Start"

    as <- getArgs
    let (proj:prims:_) = as

    -- as@(proj:prims:_) <- getArgs
    -- home_dir <- getHomeDirectory
    -- prepBase $ home_dir ++ "/Desktop/base.tar.gz"

    let m_liquid = mkLiquid as
    let m_liquid_func = mkLiquidFunc as
    let m_mapsrc = mkMapSrc as
    let m_lhlib = mkLiquidLib as
    let m_fulltest = mkLiquidFullTest as

    case m_fulltest of
      Just _ ->
        case m_liquid of
          Just l -> do
            let config = mkConfig as
            let libs = maybeToList m_mapsrc
            let lhlibs = maybeToList m_lhlib

            in_out <- testLiquidFile proj prims l libs lhlibs config

            return ()

          Nothing -> error "which file are you testing exactly?"

      Nothing ->
        case (m_liquid, m_liquid_func) of
          (Just l, Just f) -> do
              -- ghcInfos <- getGHCInfos proj [l]
              -- putStrLn . show $ length ghcInfos

              -- let specs = funcSpecs ghcInfos
              -- mapM_ (\s -> do
              --     putStrLn ""
              --     pprint s) specs

              -------

              -- let lh_names = L.map (nameOccStr . idName . mkId . fst) specs ++
              --               [l, f] ++
              --               prim_list

              -- putStrLn $ show lh_names

              let config = mkConfig as

              in_out <- findCounterExamples proj prims l (T.pack f) m_mapsrc (fmap (:[]) m_lhlib) config

              printLHOut (T.pack f) in_out
              
      
          _ -> runGHC as

runGHC :: [String] -> IO ()
runGHC as = do
    let (proj:src:lib:entry:tail_args) = as

    --Get args
    let m_assume = mAssume tail_args
    let m_assert = mAssert tail_args
    let m_reaches = mReaches tail_args

    let m_mapsrc = mkMapSrc tail_args

    let tentry = T.pack entry

    (mod_name, pre_binds, pre_tycons, pre_cls) <- translateLoaded proj src lib True m_mapsrc

    let (binds, tycons, cls) = (pre_binds, pre_tycons, pre_cls)
    let init_state = initState binds tycons cls (fmap T.pack m_assume) (fmap T.pack m_assert) (fmap T.pack m_reaches) (isJust m_assert || isJust m_reaches) tentry (Just mod_name)

    -- error $ pprExecStateStr init_state

    let init_state' = init_state

    hhp <- getZ3ProcessHandles

    let config = mkConfig as

    in_out <- run smt2 hhp config init_state'

    -- putStrLn "----------------\n----------------"

    printFuncCalls tentry in_out


printLHOut :: T.Text -> [(State, [Rule], [Expr], Expr, Maybe (Name, [Expr], Expr))] -> IO ()
printLHOut entry =
    mapM_ (\(s, _, inArg, ex, ais) -> do
        let funcCall = mkCleanExprHaskell (known_values s) (type_classes s) 
                     . foldl (\a a' -> App a a') (Var $ Id (Name entry Nothing 0) TyBottom) $ inArg

        let funcOut = mkCleanExprHaskell (known_values s) (type_classes s) $ ex

        let (n, as, out) = (case ais of
                        Just (n'@(Name n'' _ _), ais', out') -> 
                            (n''
                            , mkCleanExprHaskell (known_values s) (type_classes s) (foldl' App (Var (Id n' TyBottom)) ais')
                            , mkCleanExprHaskell (known_values s) (type_classes s) out')
                        _ -> ("", "", ""))



        -- print $ model s
        -- print inArg
        -- print ex
        -- print ais
        if funcCall == as && funcOut == out then do
            putStrLn "The call "
            putStrLn $ funcCall ++ " = " ++ funcOut
            putStrLn . T.unpack $ "violates " `T.append` entry `T.append` "'s refinement type.\n"
        else do
            putStrLn $ funcCall ++ " = " ++ funcOut
            putStrLn $ "makes a call to"
            putStrLn $ as ++ " = " ++ out
            putStrLn . T.unpack $ "violating " `T.append` n `T.append`"'s refinement type\n")

printFuncCalls :: T.Text -> [(State, [Rule], [Expr], Expr, Maybe (Name, [Expr], Expr))] -> IO ()
printFuncCalls entry =
    mapM_ (\(s, _, inArg, ex, ais) -> do
        let funcCall = mkCleanExprHaskell (known_values s) (type_classes s)
                     . foldl (\a a' -> App a a') (Var $ Id (Name entry Nothing 0) TyBottom) $ inArg

        let funcOut = mkCleanExprHaskell (known_values s) (type_classes s) $ ex

        -- print $ model s
        -- print inArg
        -- print ex
        -- print ais

        putStrLn $ funcCall ++ " = " ++ funcOut)

mAssume :: [String] -> Maybe String
mAssume a = mArg "--assume" a Just Nothing

mAssert :: [String] -> Maybe String
mAssert a = mArg "--assert" a Just Nothing

mReaches :: [String] -> Maybe String
mReaches a = mArg "--reaches" a Just Nothing

mWrapper :: [String] -> Maybe String
mWrapper a = mArg "--wrapper" a Just Nothing

mWrapWith :: [String] -> Maybe String
mWrapWith a = mArg "--wrap-with" a Just Nothing

mWrapperInt :: [String] -> Int
mWrapperInt a = mArg "--wrap-i" a read (-1)

mkPolyPred :: [String] -> Maybe String
mkPolyPred a = mArg "--poly-pred" a Just Nothing

mkPolyPredWith :: [String] -> Maybe String
mkPolyPredWith a = mArg "--poly-pred-with" a Just Nothing

mkPolyPredInt :: [String] -> Int
mkPolyPredInt a = mArg "--poly-pred-i" a read (-1)

mkLiquid :: [String] -> Maybe String
mkLiquid a = mArg "--liquid" a Just Nothing

mkLiquidFunc :: [String] -> Maybe String
mkLiquidFunc a = mArg "--liquid-func" a Just Nothing

mkMapSrc :: [String] -> Maybe String
mkMapSrc a = mArg "--mapsrc" a Just Nothing

mkLiquidLib :: [String] -> Maybe String
mkLiquidLib a = mArg "--liquid-lib" a Just Nothing

mkLiquidFullTest :: [String] -> Maybe String
mkLiquidFullTest a = mArg "--liquid-full-test" a Just Nothing

