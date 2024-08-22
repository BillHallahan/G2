{-# LANGUAGE OverloadedStrings #-}

module FuzzExecution (fuzzExecutionQuickCheck, fuzzExecution) where

import G2.Interface
import G2.Language
import G2.Language.Arbitrary
import qualified G2.Language.ExprEnv as E
import G2.Lib.Printers
import G2.Translation

import qualified Data.Text as T
import qualified Data.Text.IO as T

import GHC hiding (Name, entry)
import GHC.Paths

import TestUtils

import System.IO
import System.IO.Temp

import Test.Tasty
import Test.Tasty.QuickCheck

fuzzExecutionQuickCheck :: TestTree
fuzzExecutionQuickCheck =
    testGroup "Fuzz Execution" [
          testProperty "fuzzing execution" fuzzExecution
    ]

fuzzExecution :: StateBindingsPair () -> Property
fuzzExecution (SB init_state bindings) = do
    ioProperty (do
        config <- mkConfigTestIO

        (ers, _) <- runG2WithConfig Nothing init_state config bindings

        mr <- runGhc (Just libdir) (do
                and <$> mapM (\er -> do
                                    let s = final_state er
                                        pg = mkPrettyGuide (expr_env s, type_env s)
                                    adjustDynFlags
                                    loadStandard
                                    createDecls pg s (type_env s)
                                    case E.lookup nameCall (expr_env s) of
                                        Just e -> do
                                                    let stmt = T.unpack $ "let call :: " <> mkTypeHaskellPG pg (typeOf e) <> " = " <> printHaskellPG pg s e
                                                    _ <- execStmt stmt execOptions
                                                    return ()
                                        Nothing -> return ()
                                    validateStatesGHC pg Nothing "call" [] er) ers
            )
        
        return $ property mr)