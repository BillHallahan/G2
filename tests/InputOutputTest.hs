{-# LANGUAGE OverloadedStrings #-}
module InputOutputTest ( checkInputOutput
                       , checkInputOutputs
                       
                       , checkInputOutputsSMTStrings
                       , checkInputOutputsSMTStringsStrict
                       , checkInputOutputsSMTStringsWithSubPath
                       , checkInputOutputsQuantifiedSMTStrings

                       , checkInputOutputsSMTLists
                       
                       , checkInputOutputsTemplate
                       , checkInputOutputsWith
                       , checkInputOutputsNonRedHigher
                       , checkInputOutputsNonRedLib
                       , checkInputOutputsInstType 
                       , checkInputOutputsWithValidate
                       , checkInputOutputsWithTemplatesAndHpc) where

import Test.Tasty
import Test.Tasty.HUnit

import Control.Exception
import Data.IORef
import qualified Data.HashSet as HS
import Data.List
import qualified Data.Map.Lazy as M
import Data.Maybe
import qualified Data.Text as T
import System.FilePath
import System.IO.Unsafe
import qualified G2.Language.TyVarEnv as TV
import G2.Config
import G2.Initialization.MkCurrExpr
import G2.Interface
import G2.Language
import G2.Lib.Printers
import G2.Translation

import Reqs
import TestUtils

checkInputOutput :: FilePath -> String -> Int -> [Reqs String] -> TestTree
checkInputOutput src entry stps req = do
    checkInputOutput' mkConfigTestIO src [(entry, stps, req)]

checkInputOutputs :: FilePath -> [(String, Int, [Reqs String])] -> TestTree
checkInputOutputs src tests = do
    checkInputOutput' mkConfigTestIO src tests

checkInputOutputsSMTStrings :: FilePath -> [(String, Int, [Reqs String])] -> TestTree
checkInputOutputsSMTStrings src tests = do
    checkInputOutput' mkConfigTestWithSMTStringsIO src tests

checkInputOutputsSMTStringsStrict :: FilePath -> [(String, Int, [Reqs String])] -> TestTree
checkInputOutputsSMTStringsStrict src tests = do
    let con = (do config <- mkConfigTestWithSMTStringsIO; return $ config { smt_strings_strictness = StrictSMTStrings })
    checkInputOutput' con src tests

checkInputOutputsSMTStringsWithSubPath :: FilePath -> [(String, Int, [Reqs String])] -> TestTree
checkInputOutputsSMTStringsWithSubPath src tests = do
    let con = (do config <- mkConfigTestWithSMTStringsIO; return $ config { search_strat = Subpath })
    checkInputOutput' con src tests

checkInputOutputsQuantifiedSMTStrings :: FilePath -> [(String, Int, [Reqs String])] -> TestTree
checkInputOutputsQuantifiedSMTStrings src tests = do
    checkInputOutput' mkConfigTestWithQuantifiedSMTStringsIO src tests

checkInputOutputsSMTLists :: FilePath -> [(String, Int, [Reqs String])] -> TestTree
checkInputOutputsSMTLists src tests = do
    checkInputOutput' mkConfigTestWithSMTListsIO src tests

checkInputOutputsTemplate :: FilePath -> [(String, Int, [Reqs String])] -> TestTree
checkInputOutputsTemplate src tests = do
    checkInputOutput'
        (do config <- mkConfigTestIO; return (config { higherOrderSolver = SymbolicFunc }))
        src
        tests

checkInputOutputsWith :: FilePath -> String -> [(String, Int, [Reqs String])] -> TestTree
checkInputOutputsWith src comp_with tests = do
    checkInputOutput'
        (do config <- mkConfigTestIO; return (config { validate_with = comp_with }))
        src
        tests

checkInputOutputsNonRedHigher :: FilePath -> [(String, Int, [Reqs String])] -> TestTree
checkInputOutputsNonRedHigher src tests = do
    checkInputOutput'
        (do config <- mkConfigTestIO; return (config { higherOrderSolver = SymbolicFunc, symbolic_func_nrpc = Nrpc }))
        src
        tests

checkInputOutputsNonRedLib :: FilePath -> [(String, Int, [Reqs String])] -> TestTree
checkInputOutputsNonRedLib src tests = do
    checkInputOutput'
        (do config <- mkConfigTestIO; return (config { lib_nrpc = Nrpc, search_strat = Subpath, higherOrderSolver = SymbolicFunc }))
        src
        tests

checkInputOutputsInstType :: FilePath -> [(String, Int, [Reqs String])] -> TestTree
checkInputOutputsInstType src tests = do
    checkInputOutput'
        (do config <- mkConfigTestIO; return (config { instTV = InstAfter }))
        src
        tests

-- TODO: Remove below method and use validateState method directly. Doing so would
-- require changes in checkInputOutput'
checkInputOutputsWithValidate :: FilePath -> [(String, Int, [Reqs String])] -> TestTree
checkInputOutputsWithValidate src tests = do
    checkInputOutput'
        (do config <- mkConfigTestIO; return (config { validate = True }))
        src
        tests


checkInputOutputsWithTemplatesAndHpc :: FilePath ->[(String, Int, [Reqs String])] -> TestTree
checkInputOutputsWithTemplatesAndHpc src tests = do
    checkInputOutput'
        (do config <- mkConfigTestIO; return (config { higherOrderSolver = SymbolicFunc, hpc = True }))
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
                                               (try (checkInputOutput'' [src] exg2 mb_modname config test)
                                                    :: IO (Either SomeException ([Bool], Bool, Bool, [ExecRes ()], Bindings)))
                                let (b, e) = case r of
                                        Nothing -> (False, "\nTimeout")
                                        Just (Left e') -> (False, "\n" ++ show e')
                                        Just (Right (b_val, b_count, b_anys, exec_res, bindings)) ->
                                            let pg = mkPrettyGuide exec_res
                                                res_pretty = map (uncurry (printIO pg entry bindings)) $ zip b_val exec_res
                                                res_print = map T.unpack $ map (\(chck, (_, inp, out, _)) -> chck <> inp <> " = " <> out) res_pretty
                                            in
                                            (and b_val && b_count && b_anys, "\nvalidation = " ++ show (and b_val) ++ ", count = " ++ show b_count ++ "\n" ++ intercalate "\n" res_print)

                                assertBool ("Input/Output for file " ++ show src ++ " failed on function " ++ entry ++ "." ++ e) b 
                                )
                ) tests
    where
        printIO pg ent b val er = ((if val then "✓ " else "✗ "), printInputOutput pg (Id (Name (T.pack ent) Nothing 0 Nothing) TyUnknown) b er)
 
checkInputOutput'' :: [FilePath]
                   -> ExtractedG2
                   -> [Maybe T.Text]
                   -> Config
                   -> (String, Int, [Reqs String])
                   -> IO ([Bool], Bool, Bool, [ExecRes ()], Bindings)
checkInputOutput'' src exg2 mb_modname config (entry, stps, req) = do
    let proj = map takeDirectory src
    let config' = config { steps = stps }
        (entry_f, init_state, bindings) = initStateWithCall exg2 False (T.pack entry) mb_modname (mkCurrExpr TV.empty Nothing Nothing) (mkArgTys TV.empty) config'
    
    (r, b, _) <- runG2WithConfig proj src entry_f (T.pack entry) [] mb_modname init_state config' bindings

    let chAll = checkExprAll req
    let chAny = checkExprExists req
    (mr, anys) <- validateStates proj src (HS.fromList mb_modname) entry chAll chAny [] (validate_with config) b r
    let io = map (\(ExecRes { conc_args = i, conc_out = o}) -> i ++ [o]) r

    let chEx = checkExprInOutCount io req
    
    return (fmap (fromMaybe False) mr, chEx, anys, r, b)

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
