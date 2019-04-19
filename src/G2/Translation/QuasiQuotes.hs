module G2.Translation.QuasiQuotes (g2) where

import G2.Language.Syntax

import Control.Monad.IO.Class

import Desugar
import DynFlags
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

g2 :: QuasiQuoter
g2 = QuasiQuoter { quoteExp = parseHaskellQ
                 , quotePat = error "g2: No QuasiQuoter for patterns."
                 , quoteType = error "g2: No QuasiQuoter for types."
                 , quoteDec = error "g2: No QuasiQuoter for declarations." }

parseHaskellQ :: String -> Q Exp
parseHaskellQ s = parseHaskellQ' s >>= liftData

parseHaskellQ' :: String -> Q Expr
parseHaskellQ' s = do
    ms <- reifyModule =<< thisModule
    runIO $ do
        print ms
        parseHaskellIO s

parseHaskellIO :: String -> IO Expr
parseHaskellIO s = do
    env <- runGhc (Just libdir) getSession
    expr <- runInteractiveHsc env $ do
        maybe_stmt <- parseStmtWithLoc s
        case maybe_stmt of
            Just stmt -> do 
                (_, tc_expr, _) <- ioMsgMaybe $ tcRnStmt env stmt
                expr <- ioMsgMaybe $ deSugarExpr env tc_expr
                return expr
            Nothing -> error "g2: QuasiQuoter"
    return $ Lit (LitInt 4)


parseStmtWithLoc :: String -> Hsc (Maybe (LStmt RdrName (LHsExpr RdrName)))
parseStmtWithLoc s = do
    dflags <- getDynFlags

    let buf = stringToStringBuffer s
        loc = mkRealSrcLoc (fsLit "") 0 0

    case unP parseStmt (mkPState dflags buf loc) of
        PFailed _ err -> error "parseStmtWithLoc"
        POk _ thing -> return thing