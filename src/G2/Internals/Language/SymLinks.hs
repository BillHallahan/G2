{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module G2.Internals.Language.SymLinks ( SymLinks
                                      , empty
                                      , lookup
                                      , insert
                                      , filter
                                      , map
                                      , map'
                                      , names) where

import G2.Internals.Language.AST
import G2.Internals.Language.Naming
import G2.Internals.Language.Syntax
import Prelude hiding (filter, map, lookup)

import qualified Data.List as L
import qualified Data.Map as M

newtype SymLinks = SymLinks (M.Map Name Name)
                 deriving (Show, Eq, Read)

empty :: SymLinks
empty = SymLinks M.empty

lookup :: Name -> SymLinks -> Maybe Name
lookup name (SymLinks smap) = M.lookup name smap

insert :: Name -> Name -> SymLinks -> SymLinks
insert new old (SymLinks smap) = SymLinks (M.insert new old smap)

filter :: (Name -> Bool)  -> SymLinks -> SymLinks
filter f (SymLinks s) = SymLinks $ M.filter f s

map :: (Name -> Name)  -> SymLinks -> SymLinks
map f (SymLinks s) = SymLinks $ M.map f s

map' :: (Name -> b)  -> SymLinks -> M.Map Name b
map' f (SymLinks s) = M.map f s

names :: SymLinks -> [Name]
names (SymLinks s) = M.keys s

instance ASTContainer SymLinks Expr where
    containedASTs _ = []
    modifyContainedASTs _ m = m

instance ASTContainer SymLinks Type where
    containedASTs sym = []
    modifyContainedASTs _ m = m

instance Renamable SymLinks where
    rename old new (SymLinks m) =
        SymLinks
        . M.mapKeys (rename old new)
        . M.map (rename old new) $ m 