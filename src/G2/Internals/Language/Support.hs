module G2.Internals.Language.Support
    ( module G2.Internals.Language.Support
    , SymLinks
    ) where

import {-# SOURCE #-} G2.Internals.Language.Naming
import G2.Internals.Language.SymLinks
import G2.Internals.Language.Syntax

import qualified Data.Map as M

data State = State { expr_env :: ExprEnv
                   , type_env :: TypeEnv
                   , curr_expr :: Expr
                   , all_names :: Renamer
                   , path_conds :: [PathCond]
                   , sym_links :: SymLinks
                   , func_table :: FuncInterps
                   } deriving (Show, Eq, Read)

type ExprEnv = M.Map Name Expr

type TypeEnv = M.Map Name TyAlg

--Used in the type environment
data TyAlg = TyAlg [Name] [TyArg] deriving (Show, Eq, Read)

data TyArg = DCArg DataCon
           | FuncArg TyArg TyArg deriving (Show, Eq, Read)

data PathCond = AltCond Expr (AltCon, [Id]) Bool
              | ExtCond Expr Bool
              deriving (Show, Eq, Read)

newtype FuncInterps = FuncInterps (M.Map Name (Name, Interp))
                    deriving (Show, Eq, Read)

data Interp = StdInterp | UnInterp deriving (Show, Eq, Read)

tyArgType :: TyArg -> Type
tyArgType (DCArg (DataCon n _ _)) = TyConApp (TyCon n) []
tyArgType (DCArg (PrimCon I)) = TyInt
tyArgType (DCArg (PrimCon F)) = TyFloat
tyArgType (DCArg (PrimCon D)) = TyDouble
tyArgType (DCArg (PrimCon C)) = TyChar
tyArgType (DCArg (PrimCon B)) = TyBool
tyArgType (FuncArg t1 t2) = TyFun (tyArgType t1) (tyArgType t2)

idName :: Id -> Name
idName (Id name _) = name

lookupFuncInterps :: Name -> FuncInterps -> Maybe (Name, Interp)
lookupFuncInterps name (FuncInterps fs) = M.lookup name fs

insertFuncInterps :: Name -> (Name, Interp) -> FuncInterps -> FuncInterps
insertFuncInterps fun int (FuncInterps fs) = FuncInterps (M.insert fun int fs)

unionFuncInterps :: FuncInterps -> FuncInterps -> FuncInterps
unionFuncInterps (FuncInterps fs1) (FuncInterps fs2) = FuncInterps $ M.union fs1 fs2