module G2.Translation.HaskellCheck ( validateStates
                                   , runHPC) where

import DynFlags
import GHC hiding (Name)
import GHC.Paths

import Data.Either
import Data.List
import qualified Data.Text as T
import Text.Regex
import Unsafe.Coerce

import G2.Initialization.MkCurrExpr
import G2.Interface.OutputTypes
import G2.Language
import G2.Translation.Haskell
import G2.Translation.TransTypes
import G2.Lib.Printers

import Control.Exception

import System.Process

import Control.Monad.IO.Class

validateStates :: [FilePath] -> [FilePath] -> String -> String -> [String] -> [GeneralFlag] -> [ExecRes t] -> IO Bool
validateStates proj src modN entry chAll ghflags in_out = do
    return . all id =<< mapM (runCheck proj src modN entry chAll ghflags) in_out

-- Compile with GHC, and check that the output we got is correct for the input
runCheck :: [FilePath] -> [FilePath] -> String -> String -> [String] -> [GeneralFlag] -> ExecRes t -> IO Bool
runCheck proj src modN entry chAll gflags (ExecRes {final_state = s, conc_args = ars, conc_out = out}) = do
    (v, chAllR) <- runGhc (Just libdir) (runCheck' proj src modN entry chAll gflags s ars out)

    v' <- unsafeCoerce v :: IO (Either SomeException Bool)
    let outStr = mkCleanExprHaskell s out
    let v'' = case v' of
                    Left _ -> outStr == "error"
                    Right b -> b && outStr /= "error"

    chAllR' <- unsafeCoerce chAllR :: IO [Either SomeException Bool]
    let chAllR'' = rights chAllR'

    return $ v'' && and chAllR''

runCheck' :: [FilePath] -> [FilePath] -> String -> String -> [String] -> [GeneralFlag] -> State t -> [Expr] -> Expr -> Ghc (HValue, [HValue])
runCheck' proj src modN entry chAll gflags s ars out = do
        _ <- loadProj Nothing proj src gflags simplTranslationConfig

        let prN = mkModuleName "Prelude"
        let prImD = simpleImportDecl prN

        let exN = mkModuleName "Control.Exception"
        let exImD = simpleImportDecl exN

        let mdN = mkModuleName modN
        let imD = simpleImportDecl mdN

        setContext [IIDecl prImD, IIDecl exImD, IIDecl imD]

        let Left (v, _) = findFunc (T.pack entry) (Just $ T.pack modN) (expr_env s)
        let e = mkApp $ Var v:ars
        let arsStr = mkCleanExprHaskell s e
        let outStr = mkCleanExprHaskell s out

        let outType = mkTypeHaskell (typeOf out)

        let chck = case outStr == "error" of
                        False -> "try (evaluate (" ++ arsStr ++ " == " ++ "("
                                        ++ outStr ++ " :: " ++ outType ++ ")" ++ ")) :: IO (Either SomeException Bool)"
                        True -> "try (evaluate (" ++ arsStr ++ " == " ++ arsStr ++ ")) :: IO (Either SomeException Bool)"

        liftIO $ putStrLn chck

        v' <- compileExpr chck

        let chArgs = ars ++ [out] 
        let chAllStr = map (\f -> mkCleanExprHaskell s $ mkApp ((simpVar $ T.pack f):chArgs)) chAll
        let chAllStr' = map (\str -> "try (evaluate (" ++ str ++ ")) :: IO (Either SomeException Bool)") chAllStr

        chAllR <- mapM compileExpr chAllStr'

        return $ (v', chAllR)

simpVar :: T.Text -> Expr
simpVar s = Var (Id (Name s Nothing 0 Nothing) TyBottom)

runHPC :: FilePath -> String -> String -> [(State t, Bindings, [Expr], Expr, Maybe FuncCall)] -> IO ()
runHPC src modN entry in_out = do
    let calls = map (\(s, _, i, o, _) -> toCall entry s i o) in_out

    runHPC' src modN calls

-- Compile with GHC, and check that the output we got is correct for the input
runHPC' :: FilePath -> String -> [String] -> IO ()
runHPC' src modN ars = do
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

toCall :: String -> State t -> [Expr] -> Expr -> String
toCall entry s ars _ = mkCleanExprHaskell s $ mkApp ((simpVar $ T.pack entry):ars)

removeModule :: String -> String -> String
removeModule modN s =
    let
        r = mkRegex $ "module " ++ modN ++ " where"
    in
    subRegex r s ""
