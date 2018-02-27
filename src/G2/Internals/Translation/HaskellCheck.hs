module G2.Internals.Translation.HaskellCheck (validate) where

import GHC hiding (Name)
import GHC.Paths

import Data.Foldable
import qualified Data.Text as T
import Unsafe.Coerce

import G2.Internals.Language
import G2.Internals.Translation.Haskell
import G2.Lib.Printers

validate :: FilePath -> FilePath -> String -> String -> [String] -> [(State h t, [Expr], Expr, Maybe FuncCall)] -> IO Bool
validate proj src modN entry chAll in_out = do
	return . all id =<< mapM (\(s, i, o, _) -> runCheck proj src modN entry chAll (known_values s) (type_classes s) i o) in_out

-- Compile with GHC, and check that the output we got is correct for the input
runCheck :: FilePath -> FilePath -> String -> String -> [String] -> KnownValues -> TypeClasses -> [Expr] -> Expr -> IO Bool
runCheck proj src modN entry chAll kv tc ars out = do
    runGhc (Just libdir) $ do
        loadProj Nothing proj src False

        let prN = mkModuleName "Prelude"
        let prImD = simpleImportDecl prN

        let mdN = mkModuleName modN
        let imD = simpleImportDecl mdN

        setContext [IIDecl prImD, IIDecl imD]

        let arsStr = mkCleanExprHaskell kv tc $ mkApp ((simpVar $ T.pack entry):ars)
        let outStr = mkCleanExprHaskell kv tc out
        let chck = arsStr ++ " == " ++ outStr

        v <- compileExpr chck
        let v' = unsafeCoerce v :: Bool

        let chArgs = ars ++ [out]
        let chAllStr = map (\f -> mkCleanExprHaskell kv tc $ mkApp ((simpVar $ T.pack f):chArgs)) chAll

        chAllR <- mapM compileExpr chAllStr
        let chAllR' = unsafeCoerce chAllR :: [Bool]

        return $ v' && and chAllR'

simpVar :: T.Text -> Expr
simpVar s = Var (Id (Name s Nothing 0) TyBottom)