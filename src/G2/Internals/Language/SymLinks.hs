{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module G2.Internals.Language.SymLinks ( SymLinks
                                      , empty
                                      , lookup
                                      , insert
                                      , filter
                                      , map
                                      , map'
                                      , names
                                      , namesTypes) where

import G2.Internals.Language.AST
import G2.Internals.Language.Naming
import G2.Internals.Language.Syntax
import Prelude hiding (filter, map, lookup)

import qualified Data.List as L
import qualified Data.Map as M

newtype SymLinks = SymLinks (M.Map Name (Name, Type, Maybe Int))
                 deriving (Show, Eq, Read)

empty :: SymLinks
empty = SymLinks M.empty

lookup :: Name -> SymLinks -> Maybe (Name, Type, Maybe Int)
lookup name (SymLinks smap) = M.lookup name smap

insert :: Name -> (Name, Type, Maybe Int) -> SymLinks -> SymLinks
insert new old (SymLinks smap) = SymLinks (M.insert new old smap)

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

instance Renamable SymLinks where
    rename old new (SymLinks m) =
        SymLinks
        . M.mapKeys (rename old new)
        . M.map (\(n, t, i) ->
            (rename old new n, rename old new t, i)) $ m 

