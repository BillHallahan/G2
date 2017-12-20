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
allowedName (Name n m _) =
       all (`elem` allowedSymbol) n
    && all (`elem` allowedSymbol) (maybe "" (id) m)
    && (head n) `elem` allowedStartSymbols

cleanNames :: State -> State
cleanNames s = cleanNames' s (allNames s)

cleanNames' :: State -> [Name] -> State
cleanNames' s [] = s
cleanNames' s@State {name_gen = ng} (name@(Name n m i):ns) 
    | allowedName name = cleanNames' s ns
    | otherwise =
    let
        n' = filter (\x -> x `elem` allowedSymbol) n
        m' = fmap (filter $ \x -> x `elem` allowedSymbol) m

        -- No reserved symbols start with a $, so this ensures both uniqueness
        -- and starting with an allowed symbol
        n'' = "$" ++ n'

        (new_name, ng') = freshSeededName (Name n'' m' i) ng

        new_state = renameState name new_name 
                  $ s { name_gen = ng'}
    in
    cleanNames' new_state ns
    

allNames :: State -> [Name]
allNames s = exprNames s ++ typeNames s ++ E.keys (expr_env s) ++ M.keys (type_env s)