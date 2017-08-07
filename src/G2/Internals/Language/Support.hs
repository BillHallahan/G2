module G2.Internals.Language.Support
    ( module G2.Internals.Language.Support
    ) where

import {-# SOURCE #-} G2.Internals.Language.Naming
import G2.Internals.Language.Syntax

import qualified Data.Map as M

data State = State { expr_env :: ExprEnv
                   , type_env :: TypeEnv
                   , curr_expr :: Expr
                   , all_names :: Renamer
                   , path_conds :: [PathCond]
                   , sym_links :: SymLinks
                   , fun_table :: FuncInterps
                   } deriving (Show, Eq, Read)

type ExprEnv = M.Map Name Expr

type TypeEnv = M.Map Name Type


data PathCond = AltCond Expr (AltCon, [Id]) Bool
              | ExtCond Expr Bool
              deriving (Show, Eq, Read)

newtype SymLinks = SymLinks (M.Map Name (Name, Type, Maybe Int))
                 deriving (Show, Eq, Read)

newtype FuncInterps = FuncInterps (M.Map Name (Name, Interp))
                    deriving (Show, Eq, Read)

data Interp = StdInt | UnInt deriving (Show, Eq, Read)

idName :: Id -> Name
idName (Id name _) = name

lookupSymLinks :: Name -> SymLinks -> Maybe (Name, Type, Maybe Int)
lookupSymLinks name (SymLinks smap) = M.lookup name smap

insertSymLinks :: Name -> (Name, Type, Maybe Int) -> SymLinks -> SymLinks
insertSymLinks new old (SymLinks smap) = SymLinks (M.insert new old smap)

lookupFuncInterps :: Name -> FuncInterps -> Maybe (Name, Interp)
lookupFuncInterps name (FuncInterps fs) = M.lookup name fs

insertFuncInterps :: Name -> (Name, Interp) -> FuncInterps -> FuncInterps
insertFuncInterps fun int (FuncInterps fs) = FuncInterps (M.insert fun int fs)

