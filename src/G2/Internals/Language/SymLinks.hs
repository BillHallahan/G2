module G2.Internals.Language.SymLinks ( SymLinks
                                      , lookupSymLinks
                                      , insertSymLinks
                                      , filter
                                      , map
                                      , map'
                                      , names
                                      , namesTypes) where

import G2.Internals.Language.Syntax
import Prelude hiding (filter, map)

import qualified Data.List as L
import qualified Data.Map as M

newtype SymLinks = SymLinks (M.Map Name (Name, Type, Maybe Int))
                 deriving (Show, Eq, Read)

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