-- | NameCleaner
-- Adjusts all names in a state to ensure they will not cause problems in the SMT solver
-- In particular, we make sure that:
-- 1) Names contain only numbers, digits, and the 17 allowed symbols
-- 2) Names start with numbers or one of the 17 symbols, except for @ and .
-- 3) Names do not conflict with a symbol reserved by the SMT solver

module G2.Internals.Preprocessing.NameCleaner
    (cleanNames) where

import qualified Data.Map as M

import G2.Internals.Language
import qualified G2.Internals.Language.ExprEnv as E
-- import G2.Internals.Core.Renamer

import Debug.Trace

allowedStartSymbols =
    ['a'..'z']
    ++ ['~', '!', '$', '%', '^', '&', '*'
       --, '_' -- We eliminate this so we can use _ to seperate in string conversion
       , '-', '+', '=', '<', '>', '?', '/']

allowedSymbol = allowedStartSymbols ++ ['0'..'9'] ++ ['@', '.']

cleanNames :: State -> State
cleanNames s = trace (show $ allNames s) $ cleanNames' s (allNames s)

cleanNames' :: State -> [Name] -> State
cleanNames' s [] = s
cleanNames' s@State {name_gen = ng} (name@(Name n m i):ns) =
    let
        n' = filter (\x -> x `elem` allowedSymbol) n
        m' = fmap (filter $ \x -> x `elem` allowedSymbol) m

        -- No reserved symbols start with a $, this also ensures starting with allowed symbol
        -- We prepend a "$" to ensure that, when we append numbers in the SMT solver,
        -- we don't have conflicts with existing names ending in numbers.
        n'' = "$" ++ n'

        (new_name, ng') = freshSeededName (Name n'' m' i) ng
    in
    renameState name new_name $ s {name_gen = ng'}

allNames :: State -> [Name]
allNames s = exprNames s ++ typeNames s ++ E.keys (expr_env s) ++ M.keys (type_env s)