{-# LANGUAGE OverloadedStrings, CPP #-}

module G2.Translation.HaskellCheck ( validateStates
                                   , validateStatesGHC
                                   , loadStandard
                                   , createDeclsStr
                                   , createDecls
                                   , runHPC
                                   , adjustDynFlags ) where

#if MIN_VERSION_GLASGOW_HASKELL(9,0,2,0)
import GHC.Driver.Session
import qualified GHC.Data.EnumSet as ES
#else
import DynFlags
import qualified EnumSet as ES
#endif

import GHC hiding (Name, entry)
import GHC.LanguageExtensions

import GHC.Paths
import Data.Either
import Data.List
import qualified Data.Text as T
import Text.Regex
import Unsafe.Coerce
import qualified Data.HashMap.Lazy as H
import G2.Initialization.MkCurrExpr
import G2.Interface.ExecRes as I
import G2.Language
import G2.Translation.Haskell
import G2.Translation.Interface
import G2.Translation.TransTypes
import G2.Lib.Printers
import Control.Exception

import System.Directory
import System.FilePath
import System.IO.Error
import System.Process
import System.Timeout

import Control.Monad.IO.Class

import Debug.Trace

-- | Load the passed module(s) into GHC, and check that the `ExecRes` results are correct.
validateStates :: [FilePath] -> [FilePath] -> String -> String -> [String] -> [GeneralFlag] -> Bindings
               -> [ExecRes t]
               -> IO [Maybe Bool] -- ^ One bool per input `ExecRes`, indicating whether the results are correct or not
                                  -- Nothing in the case of a timeout  
validateStates proj src modN entry chAll gflags b in_out = do
    runGhc (Just libdir) (do
        adjustDynFlags
        loadToCheck (map dirPath src ++ proj) src modN gflags
        mapM (\er -> do
                let s = final_state er
                let pg = updatePGValNames (concatMap (map Data . dataCon) $ type_env s)
                       $ updatePGTypeNames (type_env s) $ mkPrettyGuide ()
                _ <- createDecls pg s (H.filter (\x -> adt_source x == ADTG2Generated) (type_env s))
                validateStatesGHC pg (Just $ T.pack modN) entry chAll b er) in_out)

-- | Convert g2 generated types into readable string that aim to notify the environment about the types generated by g2
-- The type is formatted as the following:
-- data name bound_ids = datacons 
creatDeclStr :: PrettyGuide -> State t -> (Name, AlgDataTy) -> String
creatDeclStr pg s (x, DataTyCon{data_cons = dcs, bound_ids = is}) =
    let
        x' = T.unpack $ printName pg x
        ids' = T.unpack . T.intercalate " " $ map (printHaskellPG pg s . Var) is
        wrapParens str = "(" <> str <> ")" 
        dc_decls = map (\dc -> printHaskellPG pg s (Data dc) <> " " <> T.intercalate " " (map (wrapParens . mkTypeHaskellPG pg) (argumentTypes dc))) dcs
        all_dc_decls = T.unpack $ T.intercalate " | " dc_decls
        derive_eq = if not (any isTyFun $ concatMap argumentTypes dcs) then " deriving Eq" else ""
    in
    "data " ++ x' ++ " " ++ ids'++ " = " ++ all_dc_decls ++ derive_eq
creatDeclStr _ _ _ = error "creatDeclStr: unsupported AlgDataTy"

-- | Compile with GHC, and check that the output we got is correct for the input
validateStatesGHC :: PrettyGuide -> Maybe T.Text -> String -> [String] -> Bindings -> ExecRes t -> Ghc (Maybe Bool)
validateStatesGHC pg modN entry chAll b er@(ExecRes {final_state = s, conc_out = out}) = do
    (v, chAllR) <- runCheck pg modN entry chAll b er

    v' <- liftIO . timeout (5 * 10 * 1000) $ (unsafeCoerce v :: IO (Either SomeException Bool))
    let outStr = T.unpack $ printHaskell s out
    let v'' = case v' of
                    Nothing -> Nothing
                    Just (Left e) | show e == "<<timeout>>" -> Nothing
                                  | otherwise -> Just (outStr == "error" || outStr == "undefined" || outStr == "?")
                    Just (Right b) -> Just (b && outStr /= "error" && outStr /= "undefined")

    chAllR' <- liftIO $ (unsafeCoerce chAllR :: IO [Either SomeException Bool])
    let chAllR'' = rights chAllR'

    return $ fmap (&& and chAllR'') v''

createDeclsStr :: PrettyGuide -> State t -> TypeEnv -> [String]
createDeclsStr pg s = map (creatDeclStr pg s) . H.toList

createDecls :: PrettyGuide -> State t -> TypeEnv -> Ghc ()
createDecls pg s = mapM_ runDecls . createDeclsStr pg s

adjustDynFlags :: Ghc ()
adjustDynFlags = do
    dyn <- getSessionDynFlags
    let dyn2 = foldl' xopt_set dyn [MagicHash, UnboxedTuples, DataKinds]
        dyn3 = wopt_unset dyn2 Opt_WarnOverlappingPatterns
        dyn4 = dyn3 { generalFlags = ES.insert Opt_Hpc (generalFlags dyn3) }
    _ <- setSessionDynFlags dyn4
    return ()

runCheck :: PrettyGuide -> Maybe T.Text -> String -> [String] -> Bindings -> ExecRes t -> Ghc (HValue, [HValue])
runCheck init_pg modN entry chAll b er@(ExecRes {final_state = s, conc_args = ars, conc_out = out}) = do
    let Left (v, _) = findFunc (T.pack entry) [modN] (expr_env s)
    let e = mkApp $ Var v:ars
    let pg = updatePGValAndTypeNames e
           . updatePGValAndTypeNames out
           $ updatePGValAndTypeNames (varIds v) init_pg
    -- let arsStr = T.unpack $ printHaskellPG pg s e
    -- let outStr = T.unpack $ printHaskellPG pg s out
    let (mvTxt, arsTxt, outTxt, _) = printInputOutput pg v b er 
        mvStr = T.unpack mvTxt
        arsStr = T.unpack arsTxt
        outStr = T.unpack outTxt

    let arsType = T.unpack $ mkTypeHaskellPG pg (typeOf e)
        outType = T.unpack $ mkTypeHaskellPG pg (typeOf out)

    -- If we are returning a primitive type (Int#, Float#, etc.) wrap in a constructor so that `==` works
    let pr_con = case typeOf out of
                        TyLitInt -> "I# "
                        TyLitDouble -> "D# "
                        TyLitFloat -> "F# "
                        TyLitChar -> "C# "
                        _ -> ""

    let chck = case outStr == "error" || outStr == "undefined" || outStr == "?" of
                    False -> mvStr ++ "Control.Exception.try (evaluate (" ++ pr_con ++ "(" ++ arsStr ++ ") == " ++ pr_con ++ "("
                                        ++ outStr ++ " :: " ++ outType ++ ")" ++ ")) :: IO (Either SomeException Bool)"
                    True -> mvStr ++ "Control.Exception.try (evaluate ( (" ++ pr_con ++ "(" ++ arsStr ++ " :: " ++ arsType ++ ")" ++
                                                    ") == " ++ pr_con ++ "(" ++ arsStr ++ "))) :: IO (Either SomeException Bool)"
    v' <- compileExpr chck

    let chArgs = ars ++ [out] 
    let chAllStr = map (\f -> T.unpack $ printHaskellPG pg s $ mkApp ((simpVar $ T.pack f):chArgs)) chAll
    let chAllStr' = map (\str -> "try (evaluate (" ++ str ++ ")) :: IO (Either SomeException Bool)") chAllStr

    chAllR <- mapM compileExpr chAllStr'

    return $ (v', chAllR)

loadToCheck :: [FilePath] -> [FilePath] -> String -> [GeneralFlag] -> Ghc ()
loadToCheck proj src modN gflags = do
        _ <- loadProj Nothing proj src gflags simplTranslationConfig

        let mdN = mkModuleName modN
        let imD = simpleImportDecl mdN

        imps <- liftIO $ concat <$> mapM getImports src

        let imp_decls = map (IIDecl . simpleImportDecl . mkModuleName) imps

        setContext (IIDecl imD:loadStandardSet ++ imp_decls)

getImports :: FilePath -> IO [String]
getImports src = do
    srcCode <- readFile src
    get srcCode
    where
        get str = do
            let r = mkRegex "^import *([a-zA-Z0-9.]*)"
            case matchRegexAll r str of
                Just (_, _, after, imps) -> (imps ++) <$> get after
                Nothing -> return []

loadStandard :: Ghc ()
loadStandard = setContext loadStandardSet

loadStandardSet :: [InteractiveImport]
loadStandardSet =
    let primN = mkModuleName "GHC.Prim"
        primImD = simpleImportDecl primN

        extsN = mkModuleName "GHC.Exts"
        extsImD = simpleImportDecl extsN

        prN = mkModuleName "Prelude"
        prImD = simpleImportDecl prN

        exN = mkModuleName "Control.Exception"
        exImD = simpleImportDecl exN

        coerceN = mkModuleName "Data.Coerce"
        coerceImD = simpleImportDecl coerceN

        charN = mkModuleName "Data.Char"
        charD = simpleImportDecl charN
    in
    [IIDecl primImD, IIDecl extsImD, IIDecl prImD, IIDecl exImD, IIDecl coerceImD, IIDecl charD]

simpVar :: T.Text -> Expr
simpVar s = Var (Id (Name s Nothing 0 Nothing) TyBottom)

runHPC :: FilePath -> String -> String -> [ExecRes t] -> IO ()
runHPC src modN entry in_out = do
    let calls = map (\(ExecRes { final_state = s, conc_args = i, conc_out = o })-> toCall entry s i o) in_out

    runHPC' src modN calls

-- Compile with GHC, and check that the output we got is correct for the input
runHPC' :: FilePath -> String -> [String] -> IO ()
runHPC' src modN ars = do
    imps <- getImports src
    srcCode <- readFile src
    let ext = dropWhile (/= '.') src
        dir = takeDirectory src
        -- srcCode' = removeModule modN srcCode

    let spces = "  "

    let chck = intercalate ("\n" ++ spces) $ map (\s -> "Ex.try (print (" ++ s ++ ")) :: IO (Either Ex.SomeException ())") ars

    let mainFunc = "\n\nmain_internal_g2 :: IO ()\nmain_internal_g2 =do\n"
                            ++ spces ++ chck ++ "\n" ++ spces ++  "return ()\n" ++ spces


    createDirectoryIfMissing False "hpc"
    let origMod = modN
        origFile = "hpc/" ++ origMod
        mainMod = "Main_" ++ modN
        mainFile = "hpc/" ++ mainMod

    let handleExists e
          | isDoesNotExistError e = return ()
          | otherwise = throwIO e
    removeFile (mainMod ++ ".tix") `catch` handleExists

    writeFile (origFile ++ ext) srcCode
    let main_imps = intercalate "\n" $ map ("import " ++) imps
    writeFile (mainFile ++ ".hs") ("module CallForHPC where\n\nimport qualified Control.Exception as Ex\nimport Data.Char\nimport " ++ modN ++ "\n" ++ main_imps ++ "\n" ++ mainFunc)

    callProcess "ghc" $ ["-main-is", "CallForHPC.main_internal_g2", "-fhpc"
                        , mainFile ++ ".hs", src, "-o", mainFile, "-O0", "-i" ++ dir]
    callProcess ("./" ++ mainFile) []

    callProcess "hpc" ["report", mainMod, "--per-module", "--srcdir=hpc", "--hpcdir=../.hpc"]

    -- putStrLn mainFunc

toCall :: String -> State t -> [Expr] -> Expr -> String
toCall entry s ars _ =
    let
        e = mkApp ((simpVar $ T.pack entry):ars)
        pg = mkPrettyGuide (exprNames e)
    in
    T.unpack . printHaskellPG pg s $ e