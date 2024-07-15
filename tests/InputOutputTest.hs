{-# LANGUAGE OverloadedStrings #-}
module InputOutputTest ( checkInputOutput
                       , checkInputOutputs
                       , checkInputOutputsTemplate
                       , checkInputOutputsNonRedTemp
                       , checkInputOutputsNonRedLib ) where

import Test.Tasty
import Test.Tasty.HUnit

import Control.Exception
import Data.IORef
import qualified Data.Map.Lazy as M
import Data.Maybe
import qualified Data.Text as T
import System.FilePath
import System.IO.Unsafe

import G2.Config
import G2.Initialization.MkCurrExpr
import G2.Interface
import G2.Language
import G2.Translation

import Reqs
import TestUtils

checkInputOutput :: FilePath -> String -> Int -> [Reqs String] -> TestTree
checkInputOutput src entry stps req = do
    checkInputOutput' mkConfigTestIO src [(entry, stps, req)]

checkInputOutputs :: FilePath -> [(String, Int, [Reqs String])] -> TestTree
checkInputOutputs src tests = do
    checkInputOutput' mkConfigTestIO src tests

checkInputOutputsTemplate :: FilePath -> [(String, Int, [Reqs String])] -> TestTree
checkInputOutputsTemplate src tests = do
    checkInputOutput'
        (do config <- mkConfigTestIO; return (config { higherOrderSolver = SymbolicFunc }))
        src
        tests

checkInputOutputsNonRedTemp :: FilePath -> [(String, Int, [Reqs String])] -> TestTree
checkInputOutputsNonRedTemp src tests = do
    checkInputOutput'
        (do config <- mkConfigTestIO; return (config { higherOrderSolver = SymbolicFuncNRPC }))
        src
        tests

checkInputOutputsNonRedLib :: FilePath -> [(String, Int, [Reqs String])] -> TestTree
checkInputOutputsNonRedLib src tests = do
    checkInputOutput'
        (do config <- mkConfigTestIO; return (config { nrpc = Nrpc }))
        src
        tests

checkInputOutputsInstType :: FilePath -> [(String, Int, [Reqs String])] -> TestTree
checkInputOutputsInstType src tests = do
    checkInputOutput'
        (do config <- mkConfigTestIO; return (config { instTV = InstAfter }))
        src
        tests


checkInputOutput' :: IO Config
                  -> FilePath
                  -> [(String, Int, [Reqs String])]
                  -> TestTree
checkInputOutput' io_config src tests = do
    let proj = takeDirectory src
    
    withResource
        (do 
            config <- io_config
            translateLoaded [proj] [src] simplTranslationConfig config
        )
        (\_ -> return ())
        $ \loadedExG2 -> 
                testGroup
                src
                $ map (\test@(entry, _, _) -> do
                        testCase (src ++ " " ++ entry) ( do
                                (mb_modname, exg2) <- loadedExG2
                                config <- io_config
                                r <- doTimeout (timeLimit config)
                                               (try (checkInputOutput'' [src] exg2 (head mb_modname) config test)
                                                    :: IO (Either SomeException (Bool, [ExecRes ()])))
                                let (b, e) = case r of
                                        Nothing -> (False, "\nTimeout")
                                        Just (Left e') -> (False, "\n" ++ show e')
                                        Just (Right (b', _)) -> (b', "")

                                assertBool ("Input/Output for file " ++ show src ++ " failed on function " ++ entry ++ "." ++ e) b 
                                )
                ) tests

checkInputOutput'' :: [FilePath]
                   -> ExtractedG2
                   -> Maybe T.Text
                   -> Config 
                   -> (String, Int, [Reqs String])
                   -> IO (Bool, [ExecRes ()])
checkInputOutput'' src exg2 mb_modname config (entry, stps, req) = do
    let config' = config { steps = stps }
        (init_state, bindings) = initStateWithCall exg2 False (T.pack entry) mb_modname (mkCurrExpr Nothing Nothing) mkArgTys config'
    
    (r, _) <- runG2WithConfig mb_modname init_state config' bindings

    let chAll = checkExprAll req
    let proj = map takeDirectory src
    mr <- validateStates proj src (T.unpack $ fromJust mb_modname) entry chAll [] r
    let io = map (\(ExecRes { conc_args = i, conc_out = o}) -> i ++ [o]) r

    let chEx = checkExprInOutCount io req
    
    return $ (mr && chEx, r)

------------

-- | Checks conditions on given expressions
checkExprAll :: [Reqs String] -> [String]
checkExprAll reqList = [f | RForAll f <- reqList]

checkExprExists :: [Reqs String] -> [String]
checkExprExists reqList = [f | RExists f <- reqList]

checkExprInOutCount :: [[Expr]] -> [Reqs c] -> Bool
checkExprInOutCount exprs reqList =
    let
        checkAtLeast = and . map ((>=) (length exprs)) $ [x | AtLeast x <- reqList]
        checkAtMost = and . map ((<=) (length exprs)) $ [x | AtMost x <- reqList]
        checkExactly = and . map ((==) (length exprs)) $ [x | Exactly x <- reqList]
    in
    checkAtLeast && checkAtMost && checkExactly
