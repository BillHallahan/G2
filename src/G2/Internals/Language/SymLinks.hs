{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module G2.Internals.Language.SymLinks ( SymLinks
                                      , empty
                                      , lookupSymLinks
                                      , insertSymLinks
                                      , filter
                                      , map
                                      , map'
                                      , names
                                      , namesTypes) where

import G2.Internals.Language.AST
import G2.Internals.Language.Syntax
import Prelude hiding (filter, map)

import qualified Data.List as L
import qualified Data.Map as M

newtype SymLinks = SymLinks (M.Map Name (Name, Type, Maybe Int))
                 deriving (Show, Eq, Read)

empty :: SymLinks
empty = SymLinks M.empty

lookupSymLinks :: Name -> SymLinks -> Maybe (Name, Type, Maybe Int)
lookupSymLinks name (SymLinks smap) = M.lookup name smap

insertSymLinks :: Name -> (Name, Type, Maybe Int) -> SymLinks -> SymLinks
insertSymLinks new old (SymLinks smap) = SymLinks (M.insert new old smap)

filter :: ((Name, Type, Maybe Int) -> Bool)  -> SymLinks -> SymLinks
filter f (SymLinks s) = SymLinks $ M.filter f s

map :: ((Name, Type, Maybe Int) -> (Name, Type, Maybe Int))  -> SymLinks -> SymLinks
map f (SymLinks s) = SymLinks $ M.map f s

map' :: ((Name, Type, Maybe Int) -> b)  -> SymLinks -> M.Map Name b
map' f (SymLinks s) = M.map f s

names :: SymLinks -> [Name]
names (SymLinks s) = M.keys s

namesTypes :: SymLinks -> [(Name, Type)]
namesTypes (SymLinks m) = L.map (\(n, (_, t, _)) -> (n, t)) $ M.toList m

instance ASTContainer SymLinks Expr where
    containedASTs _ = []
    modifyContainedASTs _ m = m

instance ASTContainer SymLinks Type where
    containedASTs sym = M.elems $ map' (\(_, t, _) -> t) sym
    modifyContainedASTs f m =
        map (\(n, t, i) -> (n, modifyContainedASTs f t, i)) m
