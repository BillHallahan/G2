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

import qualified Data.HashMap.Lazy as HM
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

cleanNames :: (ASTContainer t Expr, ASTContainer t Type, Named t) => State t -> State t
cleanNames s@State {name_gen = ng} = renames hns (s {name_gen = ng'})
  where
    (ns, ng') = createNamePairs ng . filter (not . allowedName) $ allNames s
    hns = HM.fromList ns

createNamePairs :: NameGen -> [Name] -> ([(Name, Name)], NameGen)
createNamePairs ing ins = go ing [] ins
    where
        go :: NameGen -> [(Name, Name)] -> [Name] -> ([(Name, Name)], NameGen)
        go ng rns [] = (rns, ng)
        go ng rns (name@(Name n m i l):ns) =
            let
                n' = T.filter (\x -> x `elem` allowedSymbol) n
                m' = fmap (T.filter $ \x -> x `elem` allowedSymbol) m

                -- No reserved symbols start with a $, so this ensures both uniqueness
                -- and starting with an allowed symbol
                n'' = "$" `T.append` n'

                (new_name, ng') = freshSeededName (Name n'' m' i l) ng
            in
            go ng' ((name, new_name):rns) ns

allNames :: (ASTContainer t Expr, ASTContainer t Type, Named t) => State t -> [Name]
allNames s = exprNames s ++ typeNames s ++ E.keys (expr_env s) ++ M.keys (type_env s)
