{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}

module G2.Translation.QuasiQuotes (g2) where

import G2.Config
import G2.Execution.Reducer
import G2.Initialization.MkCurrExpr
import G2.Interface.Interface
import qualified G2.Language.ExprEnv as E
import G2.Language.Support
import G2.Language.Syntax
import G2.Solver
import G2.Translation.Interface
import G2.Translation.TransTypes

import Control.Monad.IO.Class

import Data.Data
import qualified Data.HashMap.Lazy as HM
import qualified Data.Text as T
import Data.Typeable

import Language.Haskell.TH.Lib
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Quote

import System.IO
import System.IO.Temp

import System.FilePath

import Text.Regex

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
    print $ grabRegVars str
    print $ grabSymbVars str
    (_, exG2) <- withSystemTempFile "ThTemp.hs"
            (\filepath handle -> do
                hPutStrLn handle $ "module ThTemp where\ng2Expr = " ++ subSymb str
                hFlush handle
                hClose handle
                translateLoaded (takeDirectory filepath) filepath []
                    simplTranslationConfig mkConfigDef)
  
    let (s, is, b) = initState' exG2 "g2Expr" (Just "ThTemp") (mkCurrExpr Nothing Nothing) mkConfigDef

    SomeSolver con <- initSolver mkConfigDef
    case initRedHaltOrd con mkConfigDef of
        (SomeReducer red, SomeHalter hal, SomeOrderer ord) -> do
            (xs, _) <- runG2ThroughExecution red hal ord [] s b

            mapM (print . curr_expr ) xs

            let CurrExpr _ ce = curr_expr s 
            return ce

grabRegVars :: String -> [String]
grabRegVars s =
    let
        s' = dropWhile (== ' ') s
    in
    case s' of
        '\\':xs -> grabVars "->" xs
        _ -> error "Bad QuasiQuote"

afterRegVars :: String -> String
afterRegVars s = strip s
    where
        strip ('-':'>':xs) = xs
        strip (x:xs) = strip xs
        strip [] = []

grabSymbVars :: String -> [String]
grabSymbVars s =
    let
        s' = dropWhile (== ' ') $ afterRegVars s
    in
    case s' of
        '\\':xs -> grabVars "?" xs
        _ -> error "Bad QuasiQuote"

grabVars :: String -> String -> [String]
grabVars _ [] = []
grabVars en (' ':xs) = grabVars en xs
grabVars en xs
    |  take (length en) xs == en = []
grabVars en xs@(_:_) =
    let
        (x, xs') = span (/= ' ') xs
    in
    x:grabVars en xs'

-- | Replaces the first '?' with '->'
subSymb :: String -> String
subSymb = sub
    where
        sub ('?':xs) = "->" ++ xs
        sub (x:xs) = x:sub xs
        sub "" = ""

-- Modelled after dataToExpQ
dataToExpr :: Data a => (forall b . Data b => b -> Maybe (Q Expr)) -> a -> Q Expr
dataToExpr = dataToQa varOrConE litE (foldl appE)
    where
        varOrConE s =
            case nameSpace s of
                Just VarName -> return (Var undefined)
                Just DataName -> return (Data undefined)
                _ -> error "Can't construct Expr from name"

        appE x y = do
            x' <- x
            y' <- y
            return (App x' y')
        
        litE c = return (Lit undefined)