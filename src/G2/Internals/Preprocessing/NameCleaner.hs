-- | NameCleaner
-- Adjusts all names in a state to ensure they will not cause problems in the SMT solver
-- In particular, we make sure that:
-- 1) Names contain only numbers, digits, and the 17 allowed symbols
-- 2) Names start with numbers or one of the 17 symbols, except for @ and .
-- 3) Names do not conflict with a symbol reserved by the SMT solver

module G2.Internals.Preprocessing.NameCleaner (cleanNames) where

import qualified Data.Map as M

import G2.Internals.Core.Language
import G2.Internals.Core.Renamer

allowedStartSymbols =
    ['a'..'z']
    ++ ['~', '!', '$', '%', '^', '&', '*'
       , '_', '-', '+', '=', '<', '>', '?', '/']

allowedSymbol = allowedStartSymbols ++ ['0'..'9'] ++ ['@', '.']

cleanNames :: State -> State
cleanNames s = cleanNames' s (allNames s)

cleanNames' :: State -> [Name] -> State
cleanNames' s [] = s
cleanNames' s (n:ns) =
    let
        n' = filter (\x -> x `elem` allowedSymbol) n'

        -- No reserved symbols start with a $, this also ensures starting with allowed symbol
        -- We prepend a "$" to ensure that, when we append numbers in the SMT solver,
        -- we don't have conflicts with existing names ending in numbers.
        n'' = "$" ++ n' ++ "$"

        new_tenv = M.mapKeys (\k -> if k == n then n'' else k) (type_env s)
        new_eenv = M.mapKeys (\k -> if k == n then n'' else k) (expr_env s)
    in
    renameType n n'' $ renameExpr n n'' (s {type_env = new_tenv, expr_env = new_eenv})