{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module G2.Internals.Language.Support
    ( module G2.Internals.Language.AST
    , module G2.Internals.Language.Support
    , SymLinks
    ) where

import G2.Internals.Language.AST
import G2.Internals.Language.Naming
import G2.Internals.Language.SymLinks
import G2.Internals.Language.Syntax

import qualified Data.Map as M

data State = State { expr_env :: ExprEnv
                   , type_env :: TypeEnv
                   , curr_expr :: Expr
                   , all_names :: NameGen
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

data PathCond = AltCond Expr AltMatch Bool
              | ExtCond Expr Bool
              deriving (Show, Eq, Read)

newtype FuncInterps = FuncInterps (M.Map Name (Name, Interp))
                    deriving (Show, Eq, Read)

data Interp = StdInterp | UnInterp deriving (Show, Eq, Read)

tyArgType :: TyArg -> Type
tyArgType (DCArg (DataCon n _ _)) = TyConApp n []
tyArgType (DCArg (PrimCon I)) = TyInt
tyArgType (DCArg (PrimCon F)) = TyFloat
tyArgType (DCArg (PrimCon D)) = TyDouble
tyArgType (DCArg (PrimCon C)) = TyChar
tyArgType (DCArg (PrimCon B)) = TyBool
tyArgType (FuncArg t1 t2) = TyFun (tyArgType t1) (tyArgType t2)

lookupFuncInterps :: Name -> FuncInterps -> Maybe (Name, Interp)
lookupFuncInterps name (FuncInterps fs) = M.lookup name fs

insertFuncInterps :: Name -> (Name, Interp) -> FuncInterps -> FuncInterps
insertFuncInterps fun int (FuncInterps fs) = FuncInterps (M.insert fun int fs)

unionFuncInterps :: FuncInterps -> FuncInterps -> FuncInterps
unionFuncInterps (FuncInterps fs1) (FuncInterps fs2) = FuncInterps $ M.union fs1 fs2

-- | TypeClass definitions
instance AST TyArg where
    children (FuncArg t1 t2) = [t1, t2]
    children _ = []

    modifyChildren f (FuncArg t1 t2) = FuncArg (f t1) (f t2)
    modifyChildren _ a = a

instance ASTContainer State Expr where
    containedASTs s = ((containedASTs . type_env) s) ++
                      ((containedASTs . expr_env) s) ++
                      ((containedASTs . curr_expr) s) ++
                      ((containedASTs . path_conds) s) ++
                      ((containedASTs . sym_links) s)

    modifyContainedASTs f s = s { type_env  = (modifyASTs f . type_env) s
                                , expr_env  = (modifyASTs f . expr_env) s
                                , curr_expr = (modifyASTs f . curr_expr) s
                                , path_conds = (modifyASTs f . path_conds) s
                                , sym_links = (modifyASTs f . sym_links) s }


instance ASTContainer State Type where
    containedASTs s = ((containedASTs . expr_env) s) ++
                      ((containedASTs . type_env) s) ++
                      ((containedASTs . curr_expr) s) ++
                      ((containedASTs . path_conds) s) ++
                      ((containedASTs . sym_links) s)

    modifyContainedASTs f s = s { type_env  = (modifyASTs f . type_env) s
                                , expr_env  = (modifyASTs f . expr_env) s
                                , curr_expr = (modifyASTs f . curr_expr) s
                                , path_conds = (modifyASTs f . path_conds) s
                                , sym_links = (modifyASTs f . sym_links) s }

instance ASTContainer TyAlg Expr where
    containedASTs _ = []
    modifyContainedASTs _ a = a

instance ASTContainer TyAlg Type where
    containedASTs (TyAlg _ dc) = containedASTs dc
    modifyContainedASTs f (TyAlg ns dc) = TyAlg ns (modifyContainedASTs f dc)

instance ASTContainer TyArg Expr where
    containedASTs _ = []
    modifyContainedASTs _ a = a

instance ASTContainer TyArg Type where
    containedASTs (DCArg dc) = containedASTs dc
    containedASTs (FuncArg t1 t2) = containedASTs t1 ++ containedASTs t2

    modifyContainedASTs f (DCArg dc) = DCArg (modifyContainedASTs f dc)
    modifyContainedASTs f (FuncArg t1 t2) =
        FuncArg (modifyContainedASTs f t1) (modifyContainedASTs f t2)

instance ASTContainer PathCond Expr where
    containedASTs (ExtCond e _ )   = [e]
    containedASTs (AltCond e _ _) = [e]

    modifyContainedASTs f (ExtCond e b) = ExtCond (modifyContainedASTs f e) b
    modifyContainedASTs f (AltCond e a b) =
        AltCond (modifyContainedASTs f e) a b

instance ASTContainer PathCond Type where
    containedASTs (ExtCond e _)   = containedASTs e
    containedASTs (AltCond e a _) = containedASTs e ++ containedASTs a

    modifyContainedASTs f (ExtCond e b) = ExtCond e' b
      where e' = modifyContainedASTs f e
    modifyContainedASTs f (AltCond e a b) = AltCond e' a' b
      where e' = modifyContainedASTs f e
            a' = modifyContainedASTs f a

instance ASTContainer TyAlg TyArg where
    containedASTs (TyAlg _ ta) = ta

    modifyContainedASTs f (TyAlg n ta) = TyAlg n (modifyContainedASTs f ta)