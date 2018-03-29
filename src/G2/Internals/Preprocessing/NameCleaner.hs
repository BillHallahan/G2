{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}

-- | NameCleaner
-- Adjusts all names in a state to ensure they will not cause problems in the SMT solver
-- In particular, we make sure that:
-- 1) Names contain only numbers, digits, and the 17 allowed symbols
-- 2) Names start with numbers or one of the 17 symbols, except for @ and .
-- 3) Names do not conflict with a symbol reserved by the SMT solver

module G2.Internals.Preprocessing.NameCleaner
    ( cleanNames
    , allowedStartSymbols
    , allowedSymbol
    ) where

import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Text as T

import G2.Internals.Language
import qualified G2.Internals.Language.ExprEnv as E

allowedStartSymbols :: [Char]
allowedStartSymbols =
    ['a'..'z'] ++ ['A'..'Z']
    ++ ['~', '!', '$', '%', '^', '&', '*'
       -- We eliminate '_' so we can use '_' to seperate in string conversions
       -- (see nameToStr in Naming.hs)
       --, '_'
       , '-', '+', '=', '<', '>', '?', '/']

allowedSymbol :: [Char]
allowedSymbol = allowedStartSymbols ++ ['0'..'9'] ++ ['@', '.']

allowedName :: Name -> Bool
allowedName (Name n m _ _) =
       T.all (`elem` allowedSymbol) n
    && T.all (`elem` allowedSymbol) (maybe "" (id) m)
    && (T.head n) `elem` allowedStartSymbols

cleanNames :: (ASTContainer h Expr, ASTContainer t Expr, ASTContainer h Type, ASTContainer t Type, Named h, Named t) => State h t -> State h t
cleanNames s = cleanNames' s (L.nub $ allNames s)

cleanNames' :: (ASTContainer h Expr, ASTContainer t Expr, ASTContainer h Type, ASTContainer t Type, Named h, Named t) => State h t -> [Name] -> State h t
cleanNames' s [] = s
cleanNames' s@State {name_gen = ng} (name@(Name n m i l):ns) 
    | allowedName name = cleanNames' s ns
    | otherwise =
    let
        n' = T.filter (\x -> x `elem` allowedSymbol) n
        m' = fmap (T.filter $ \x -> x `elem` allowedSymbol) m

        -- No reserved symbols start with a $, so this ensures both uniqueness
        -- and starting with an allowed symbol
        n'' = "$" `T.append` n'

        (new_name, ng') = freshSeededName (Name n'' m' i l) ng

        new_state = rename name new_name 
                  $ s { name_gen = ng'}
    in
    cleanNames' new_state ns

-- allNames :: State -> [Name]
-- allNames s = exprNames s ++ E.keys (expr_env s)

allNames :: (ASTContainer h Expr, ASTContainer t Expr, ASTContainer h Type, ASTContainer t Type, Named h, Named t) => State h t -> [Name]
allNames s = exprNames s ++ typeNames s ++ E.keys (expr_env s) ++ M.keys (type_env s)
