{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}

module G2.Translation.QuasiQuotes (g2) where

import G2.Config
import G2.Execution.Reducer
import G2.Initialization.MkCurrExpr
import G2.Interface.Interface
import G2.Language.Support
import G2.Language.Syntax
import G2.Solver
import G2.Translation.Interface
import G2.Translation.TransTypes

import Data.Data
import qualified Data.Text as T

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
parseHaskellQ str = do
    (s, _) <- parseHaskellQ' str

    let CurrExpr _ ce = curr_expr $ head s

    exp <- dataToExpQ (\a -> liftText <$> cast a) ce

    addRegVarBindings str exp
    where
        liftText txt = AppE (VarE 'T.pack) <$> lift (T.unpack txt)

parseHaskellQ' :: String -> Q ([State ()], Bindings)
parseHaskellQ' s = do
    ms <- reifyModule =<< thisModule
    runIO $ do
        print ms
        parseHaskellIO s

-- | Turn the Haskell into a G2 Expr.  All variables- both those that the user
-- marked to be passed into the Expr as real values, and those that the user
-- wants to solve for- are treated as symbolic here.
parseHaskellIO :: String -> IO ([State ()], Bindings)
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
            xsb@(xs, _) <- runG2ThroughExecution red hal ord [] s b

            mapM_ (\st -> do
                print . curr_expr $ st
                print . path_conds $ st) xs

            return xsb

-- | Adds the appropriate number of lambda bindings to the Exp
addRegVarBindings :: String -> Exp -> Q Exp
addRegVarBindings str exp = do
    let regs = grabRegVars str

    ns <- mapM newName regs
    let ns_pat = map VarP ns

    return $ foldr (\n -> LamE [n]) exp ns_pat

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
dataToExpr = dataToQa vOrCE lE (foldl apE)
    where
        vOrCE s =
            case nameSpace s of
                Just VarName -> return (Var undefined)
                Just DataName -> return (Data undefined)
                _ -> error "Can't construct Expr from name"

        apE x y = do
            x' <- x
            y' <- y
            return (App x' y')
        
        lE c = return (Lit undefined)