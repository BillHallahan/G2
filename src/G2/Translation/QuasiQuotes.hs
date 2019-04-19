{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

module G2.Translation.QuasiQuotes (g2) where

import G2.Config
import G2.Interface.Interface
import G2.Language.Support
import G2.Language.Syntax
import G2.Translation.Interface
import G2.Translation.TransTypes

import Control.Monad.IO.Class

import qualified Data.HashMap.Lazy as HM
import qualified Data.Text as T
import Data.Typeable

import Bag
import Desugar
import DynFlags
import ErrUtils
import FastString
import HscMain
import HscTypes
import GHC
import GHC.Paths
import Lexer
import Parser
import SrcLoc
import StringBuffer
import TcRnDriver

import Language.Haskell.TH.Lib
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Quote

import System.IO
import System.IO.Temp

import System.FilePath

g2 :: QuasiQuoter
g2 = QuasiQuoter { quoteExp = parseHaskellQ
                 , quotePat = error "g2: No QuasiQuoter for patterns."
                 , quoteType = error "g2: No QuasiQuoter for types."
                 , quoteDec = error "g2: No QuasiQuoter for declarations." }

parseHaskellQ :: String -> Q Exp
parseHaskellQ s = parseHaskellQ' s >>= dataToExpQ (\a -> liftText <$> cast a)
    where
        liftText txt = AppE (VarE 'T.pack) <$> lift (T.unpack txt)


parseHaskellQ' :: String -> Q Expr
parseHaskellQ' s = do
    ms <- reifyModule =<< thisModule
    runIO $ do
        print ms
        parseHaskellIO s

parseHaskellIO :: String -> IO Expr
parseHaskellIO str = do
    (_, exG2) <- withSystemTempFile "ThTemp.hs"
            (\filepath handle -> do
                hPutStrLn handle $ "module ThTemp where\ng2Expr = " ++ str
                hFlush handle
                hClose handle
                translateLoaded (takeDirectory filepath) filepath []
                    simplTranslationConfig mkConfigDef)
                -- hskToG2ViaCgGutsFromFile
                --     (Just HscInterpreted)
                --     (takeDirectory filepath)
                --     filepath
                --     HM.empty
                --     HM.empty
                --     simplTranslationConfig)
  
    let (s, is, b) = initState' exG2 "g2Expr" (Just "ThTemp") mkConfigDef

    putStrLn $ show s
    let CurrExpr _ ce = curr_expr s 
    return ce


{-
parseHaskellIO s = do
    env <- runGhc (Just libdir) getSession
    expr <- runInteractiveHsc env $ do
        maybe_stmt <- parseStmtWithLoc s
        case maybe_stmt of
            Just stmt -> do
                (_, tc_expr, _) <- ioMsgMaybe2 $ tcRnStmt env stmt
                liftIO $ putStrLn "Here 3"
                expr <- ioMsgMaybe $ deSugarExpr env tc_expr
                return expr
            Nothing -> error "g2: QuasiQuoter"
    return $ mkExpr HM.empty HM.empty Nothing expr
-}

-------

parseStmtWithLoc :: String -> Hsc (Maybe (LStmt RdrName (LHsExpr RdrName)))
parseStmtWithLoc s = do
    dflags <- getDynFlags

    liftIO $ putStrLn "Here 1"

    let buf = stringToStringBuffer s
        loc = mkRealSrcLoc (fsLit "") 0 0

    liftIO $ putStrLn "Here 2"

    case unP parseStmt (mkPState dflags buf loc) of
        PFailed _ err -> error "parseStmtWithLoc"
        POk _ thing -> return thing

ioMsgMaybe2 :: IO (Messages, Maybe a) -> Hsc a
ioMsgMaybe2 ioA = do
    ((warns,errs), mb_r) <- liftIO ioA
    case mb_r of
        Nothing -> error "Nothing"
        Just r  -> return r

-- 
