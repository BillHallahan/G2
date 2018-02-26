{-# LANGUAGE OverloadedStrings #-}
module InputOutputTest where

import Test.Tasty
import Test.Tasty.HUnit

import GHC
import GHC.Paths

import Control.Exception
import Data.Foldable
import qualified Data.Text as T
import Unsafe.Coerce

import G2.Internals.Config
import G2.Internals.Execution
import G2.Internals.Interface
import G2.Internals.Language
import G2.Internals.Translation
import G2.Internals.Solver
import G2.Lib.Printers

-- check :: IO ()
-- check = do
--     v' <- runGhc (Just libdir) $ do
--         loadProj Nothing "./tests/Samples" "./tests/Samples/HigherOrderMath.hs" False
--         let prN = mkModuleName "Prelude"
--         let prImD = simpleImportDecl prN

--         let mdN = mkModuleName "HigherOrderMath"
--         let imD = simpleImportDecl mdN

--         setContext [IIDecl prImD, IIDecl imD]
--         v <- compileExpr "abs2 (-54) == 54.5"
--         return (unsafeCoerce v :: Bool)
--     print v'

checkInputOutput :: FilePath -> FilePath -> String -> String ->  IO TestTree
checkInputOutput proj src md entry = checkInputOutputWithConfig proj src md entry mkConfigDef

checkInputOutputWithConfig :: FilePath -> FilePath -> String -> String -> Config -> IO TestTree
checkInputOutputWithConfig proj src md entry config = do
    r <- checkInputOutput' proj src md entry config

    let ch = case r of
            Left _ -> False
            Right b -> b

    return . testCase src $ assertBool ("Input/Output for file " ++ show src ++ " failed on function " ++ entry ++ ".") ch

checkInputOutput' :: FilePath -> FilePath -> String -> String -> Config -> IO (Either SomeException Bool)
checkInputOutput' proj src md entry config = try (checkInputOutput'' proj src md entry config)

checkInputOutput'' :: FilePath -> FilePath -> String -> String -> Config -> IO Bool
checkInputOutput'' proj src md entry config = do
    (mb_modname, binds, tycons, cls, _) <- translateLoaded proj src [] False config

    let init_state = initState binds tycons cls Nothing Nothing Nothing False (T.pack entry) mb_modname
    let halter_set_state = init_state {halter = steps config}
    
    (con, hhp) <- getSMT config

    r <- run stdReduce halterIsZero halterSub1 executeNext con hhp config halter_set_state

    return . all id =<< mapM (\(s, i, o, _) -> check proj src md entry (known_values s) i o) r

-- Compile with GHC, and check that the output we got is correct for the input
check :: FilePath -> FilePath -> String -> String -> KnownValues -> [Expr] -> Expr -> IO Bool
check proj src modN entry kv ars out = do
    runGhc (Just libdir) $ do
        loadProj Nothing proj src False

        let prN = mkModuleName "Prelude"
        let prImD = simpleImportDecl prN

        let mdN = mkModuleName modN
        let imD = simpleImportDecl mdN

        setContext [IIDecl prImD, IIDecl imD]

        let arsStr = mkExprHaskell kv $ foldl' App (Var (Id (Name (T.pack entry) Nothing 0) TyBottom)) ars
        let outStr = mkExprHaskell kv out
        let chck = arsStr ++ " == " ++ outStr

        v <- compileExpr chck
        
        return (unsafeCoerce v :: Bool)