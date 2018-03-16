module G2.Internals.Translation.HaskellCheck ( validateStates
                                             , runHPC) where

import DynFlags
import GHC hiding (Name)
import GHC.Paths

import Data.Foldable
import Data.List
import qualified Data.Text as T
import Text.Regex
import Unsafe.Coerce

import G2.Internals.Language
import G2.Internals.Translation.Haskell
import G2.Lib.Printers

import System.Directory
import System.Process

validateStates :: FilePath -> FilePath -> String -> String -> [String] -> [GeneralFlag] -> [(State h t, [Expr], Expr, Maybe FuncCall)] -> IO Bool
validateStates proj src modN entry chAll ghflags in_out = do
    return . all id =<< mapM (\(s, i, o, _) -> runCheck proj src modN entry chAll ghflags s i o) in_out

-- Compile with GHC, and check that the output we got is correct for the input
runCheck :: FilePath -> FilePath -> String -> String -> [String] -> [GeneralFlag] -> State h t -> [Expr] -> Expr -> IO Bool
runCheck proj src modN entry chAll gflags s ars out = do
    runGhc (Just libdir) $ do
        loadProj Nothing proj src gflags False

        let prN = mkModuleName "Prelude"
        let prImD = simpleImportDecl prN

        let mdN = mkModuleName modN
        let imD = simpleImportDecl mdN

        setContext [IIDecl prImD, IIDecl imD]

        let arsStr = mkCleanExprHaskell s $ mkApp ((simpVar $ T.pack entry):ars)
        let outStr = mkCleanExprHaskell s out
        let chck = case outStr == "error" of
                        False -> arsStr ++ " == " ++ outStr
                        True -> "True"

        v <- compileExpr chck
        let v' = unsafeCoerce v :: Bool

        let chArgs = ars ++ [out]
        let chAllStr = map (\f -> mkCleanExprHaskell s $ mkApp ((simpVar $ T.pack f):chArgs)) chAll

        chAllR <- mapM compileExpr chAllStr
        let chAllR' = unsafeCoerce chAllR :: [Bool]

        return $ v' && and chAllR'

simpVar :: T.Text -> Expr
simpVar s = Var (Id (Name s Nothing 0) TyBottom)

runHPC :: FilePath -> FilePath -> String -> String -> [(State h t, [Expr], Expr, Maybe FuncCall)] -> IO ()
runHPC proj src modN entry in_out = do
    let calls = map (\(s, i, o, _) -> toCall entry s i o) in_out

    runHPC' proj src modN calls

-- Compile with GHC, and check that the output we got is correct for the input
runHPC' :: FilePath -> FilePath -> String -> [String] -> IO ()
runHPC' proj src modN ars = do
    srcCode <- readFile src
    let srcCode' = removeModule modN srcCode

    let spces = "  "

    let chck = intercalate ("\n" ++ spces) $ map (\s -> "print (" ++ s ++ ")") ars

    let mainFunc = "\n\nmain :: IO ()\nmain =do\n" ++ spces ++ chck ++ "\n" ++ spces

    let mainN = "Main_" ++ modN

    writeFile (mainN ++ ".hs") (srcCode' ++ mainFunc)

    callProcess "ghc" ["-fhpc", mainN ++ ".hs"]
    callProcess ("./" ++ mainN) []

    callProcess "hpc" ["report", mainN]

    -- putStrLn mainFunc

toCall :: String -> State h t -> [Expr] -> Expr -> String
toCall entry s ars _ = mkCleanExprHaskell s $ mkApp ((simpVar $ T.pack entry):ars)

removeModule :: String -> String -> String
removeModule modN s =
    let
        r = mkRegex $ "module " ++ modN ++ " where"
    in
    subRegex r s ""