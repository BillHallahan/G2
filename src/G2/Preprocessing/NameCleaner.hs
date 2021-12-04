{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}

-- | NameCleaner
-- Adjusts all names in a state to ensure they will not cause problems in the SMT solver
-- In particular, we make sure that:
-- 1) Names contain only numbers, digits, and the 17 allowed symbols
-- 2) Names start with numbers or one of the 17 symbols, except for @ and .
-- 3) Names do not conflict with a symbol reserved by the SMT solver

module G2.Preprocessing.NameCleaner
    ( cleanNames
    , cleanNames'
    , cleanNamesFromList
    , allowedStartSymbols
    , allowedSymbol
    , cleanName
    ) where

import Data.Foldable
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as S
import qualified Data.Text as T

import G2.Language
import qualified G2.Language.ExprEnv as E

allowedStartSymbols :: S.HashSet Char
allowedStartSymbols = S.fromList $
    ['a'..'z'] ++ ['A'..'Z']
    ++ ['~', '!', '$', '%', '^', '&', '*'
       -- We eliminate '_' so we can use '_' to seperate in string conversions
       -- (see nameToStr in Naming.hs)
       --, '_'
       , '-', '+', '=', '<', '>', '?', '/']

allowedSymbol :: S.HashSet Char
allowedSymbol = allowedStartSymbols `S.union` S.fromList (['0'..'9'] ++ ['@', '.'])

allowedName :: Name -> Bool
allowedName (Name n m _ _) =
       T.all (`S.member` allowedSymbol) n
    && T.all (`S.member` allowedSymbol) (maybe "" (id) m)
    && (T.head n) `S.member` allowedStartSymbols

-- Note that the list of names in cleanNames is NOT the list of all names in the State.
-- For efficiencies reasons, we aim to clean only those names that may be used
-- in the SMT formulas.  For this reason, cleanNames is not defined in terms of
-- the more general cleanNames'.

-- cleanNames :: (ASTContainer t Expr, ASTContainer t Type, Named t) => State t -> Bindings -> (State t, Bindings)
-- cleanNames s b@Bindings {name_gen = ng} = (renames hns s, b {name_gen = ng'})
cleanNames :: (ASTContainer t Expr, ASTContainer t Type, Named t) => State t -> CleanedNames -> NameGen -> (State t, CleanedNames, NameGen)
cleanNames s cl_names ng = (renames hns s, cl_names', ng')
  where
    (ns, ng') = createNamePairs ng . filter (not . allowedName) . map idName . E.symbolicIds $ expr_env s -- ++ altIds s
    hns = HM.fromList ns
    cl_names' = foldr (\(old, new) -> HM.insert new old) cl_names (HM.toList hns)


cleanNames' :: Named n => NameGen -> n -> (n, NameGen)
cleanNames' ng n = (renames hns n, ng')
    where
      (ns, ng') = createNamePairs ng . filter (not . allowedName) . toList $ names n
      hns = HM.fromList ns

cleanNamesFromList :: Named n => NameGen -> [Name] -> n -> (n, NameGen)
cleanNamesFromList ng ns n = (renames hns n, ng')
    where
      (ns', ng') = createNamePairs ng . filter (not . allowedName) . toList $ names ns
      hns = HM.fromList ns'

createNamePairs :: NameGen -> [Name] -> ([(Name, Name)], NameGen)
createNamePairs ing ins = go ing [] ins
    where
        go :: NameGen -> [(Name, Name)] -> [Name] -> ([(Name, Name)], NameGen)
        go ng rns [] = (rns, ng)
        go ng rns (name:ns) =
            let
                name' = cleanName name
                (new_name, ng') = freshSeededName name' ng
            in
            go ng' ((name, new_name):rns) ns

cleanName :: Name -> Name
cleanName nm@(Name n m i l)
  | allowedName nm = nm
  | otherwise = 
      let
          n' = T.filter (\x -> x `S.member` allowedSymbol) n
          m' = fmap (T.filter $ \x -> x `S.member` allowedSymbol) m

          -- No reserved symbols start with a $, so this ensures both uniqueness
          -- and starting with an allowed symbol
          n'' = "$" `T.append` n'
      in
      Name n'' m' i l
