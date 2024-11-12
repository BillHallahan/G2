{-# LANGUAGE OverloadedStrings, CPP #-}

module G2.Translation.HaskellCheck ( validateStates
                                   , validateStatesGHC
                                   , loadStandard
                                   , createDeclsStr
                                   , createDecls
                                   , adjustDynFlags
                                   , runHPC) where

#if MIN_VERSION_GLASGOW_HASKELL(9,0,2,0)
import GHC.Driver.Session
#else
import DynFlags
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
import G2.Translation.TransTypes
import G2.Lib.Printers
import Control.Exception

import System.Process

import Control.Monad.IO.Class

-- | Load the passed module(s) into GHC, and check that the `ExecRes` results are correct.
validateStates :: [FilePath] -> [FilePath] -> String -> String -> [String] -> [GeneralFlag] -> Bindings -> [ExecRes t] -> IO Bool
validateStates proj src modN entry chAll gflags b in_out = do
    and <$> runGhc (Just libdir) (do
        adjustDynFlags
        loadToCheck proj src modN gflags
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
validateStatesGHC :: PrettyGuide -> I.ModuleName -> String -> [String] -> Bindings -> ExecRes t -> Ghc Bool
validateStatesGHC pg modN entry chAll b er@(ExecRes {final_state = s, conc_out = out}) = do
    (v, chAllR) <- runCheck pg modN entry chAll b er

    v' <- liftIO $ (unsafeCoerce v :: IO (Either SomeException Bool))
    let outStr = T.unpack $ printHaskell s out
    let v'' = case v' of
                    Left _ -> outStr == "error" || outStr == "undefined"
                    Right b -> b && outStr /= "error" && outStr /= "undefined"

    chAllR' <- liftIO $ (unsafeCoerce chAllR :: IO [Either SomeException Bool])
    let chAllR'' = rights chAllR'

    return $ v'' && and chAllR''

createDeclsStr :: PrettyGuide -> State t -> TypeEnv -> [String]
createDeclsStr pg s = map (creatDeclStr pg s) . H.toList

createDecls :: PrettyGuide -> State t -> TypeEnv -> Ghc ()
createDecls pg s = mapM_ runDecls . createDeclsStr pg s

adjustDynFlags :: Ghc ()
adjustDynFlags = do
    dyn <- getSessionDynFlags
    let dyn' = foldl' xopt_set dyn [MagicHash, UnboxedTuples, DataKinds]
        dyn'' = wopt_unset dyn' Opt_WarnOverlappingPatterns
    _ <- setSessionDynFlags dyn''
    return ()

runCheck :: PrettyGuide -> I.ModuleName -> String -> [String] -> Bindings -> ExecRes t -> Ghc (HValue, [HValue])
runCheck init_pg modN entry chAll b er@(ExecRes {final_state = s, conc_args = ars, conc_out = out}) = do
    let Left (v, _) = findFunc (T.pack entry) [modN] (expr_env s)
    let e = mkApp $ Var v:ars
    let pg = updatePGValAndTypeNames e
           . updatePGValAndTypeNames out
           $ updatePGValAndTypeNames (varIds v) init_pg
    -- let arsStr = T.unpack $ printHaskellPG pg s e
    -- let outStr = T.unpack $ printHaskellPG pg s out
    let (mvTxt, arsTxt, outTxt) = printInputOutput pg v b er 
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

    let chck = case outStr == "error" || outStr == "undefined" of
                    False -> mvStr ++ "try (evaluate (" ++ pr_con ++ "(" ++ arsStr ++ ") == " ++ pr_con ++ "("
                                        ++ outStr ++ " :: " ++ outType ++ ")" ++ ")) :: IO (Either SomeException Bool)"
                    True -> mvStr ++ "try (evaluate ( (" ++ pr_con ++ "(" ++ arsStr ++ " :: " ++ arsType ++ ")" ++
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

        setContext (IIDecl imD:loadStandardSet)

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
toCall entry s ars _ = T.unpack . printHaskell s $ mkApp ((simpVar $ T.pack entry):ars)

removeModule :: String -> String -> String
removeModule modN s =
    let
        r = mkRegex $ "module " ++ modN ++ " where"
    in
    subRegex r s ""
