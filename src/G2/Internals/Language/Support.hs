{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module G2.Internals.Language.Support
    ( module G2.Internals.Language.AST
    , module G2.Internals.Language.Support
    , SymLinks
    ) where

import G2.Internals.Language.AST
import G2.Internals.Language.Naming
import G2.Internals.Language.SymLinks hiding (filter)
import G2.Internals.Language.Syntax

import qualified Data.Map as M

-- | The State is something that is passed around in G2. It can be utilized to
-- perform defunctionalization, execution, and SMT solving on.
data State = State { expr_env :: ExprEnv
                   , type_env :: TypeEnv
                   , curr_expr :: Expr
                   , name_gen :: NameGen
                   , path_conds :: [PathCond]
                   , sym_links :: SymLinks
                   , func_table :: FuncInterps
                   } deriving (Show, Eq, Read)

-- | Expression environments are mappings form names to expressions. These are
-- typically used for variable lookups during execution.
type ExprEnv = M.Map Name Expr

-- | Type environments map names of types to their appropriate types. However
-- our primary interest with these is for dealing with algebraic data types,
-- and we only store those information accordingly.
type TypeEnv = M.Map Name AlgDataTy

-- | Algebraic data types are types constructed with parametrization of some
-- names over types, and a list of data constructors for said type.
data AlgDataTy = AlgDataTy [Name] [DataCon] deriving (Show, Eq, Read)

-- | Path conditions represent logical constraints on our current execution
-- path. We can have path constraints enforced due to case/alt branching, due
-- to assertion / assumptions made, or some externally coded factors.
data PathCond = AltCond Expr AltMatch Bool
              | ExtCond Expr Bool
              deriving (Show, Eq, Read)

-- | Function interpretation table. Maps functions to their interpretations.
newtype FuncInterps = FuncInterps (M.Map Name (Name, Interp))
                    deriving (Show, Eq, Read)

-- | Functions can have a standard interpretation or be uninterpreted.
data Interp = StdInterp | UnInterp deriving (Show, Eq, Read)

-- | Naive expression lookup by only the occurrence name string.
naiveLookup :: String -> ExprEnv -> [(Name, Expr)]
naiveLookup key eenv = filter (\(Name occ _ _, _) -> occ == key) (M.toList eenv)

emptyFuncInterps :: FuncInterps
emptyFuncInterps = FuncInterps M.empty

-- | Do some lookups into the function interpretation table.
lookupFuncInterps :: Name -> FuncInterps -> Maybe (Name, Interp)
lookupFuncInterps name (FuncInterps fs) = M.lookup name fs

-- | Add some items into the function interpretation table.
insertFuncInterps :: Name -> (Name, Interp) -> FuncInterps -> FuncInterps
insertFuncInterps fun int (FuncInterps fs) = FuncInterps (M.insert fun int fs)

-- | You can also join function interpretation tables?! Note: only
-- reasonable if the union of their key set all map to the same elements.
unionFuncInterps :: FuncInterps -> FuncInterps -> FuncInterps
unionFuncInterps (FuncInterps fs1) (FuncInterps fs2) = FuncInterps $ M.union fs1 fs2

-- | TypeClass definitions
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

instance ASTContainer AlgDataTy Expr where
    containedASTs _ = []
    modifyContainedASTs _ a = a

instance ASTContainer AlgDataTy Type where
    containedASTs (AlgDataTy _ dcs) = containedASTs dcs
    modifyContainedASTs f (AlgDataTy ns dcs) = AlgDataTy ns (modifyContainedASTs f dcs)

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



instance ASTContainer AlgDataTy DataCon where
    containedASTs (AlgDataTy _ dcs) = dcs

    modifyContainedASTs f (AlgDataTy ns dcs) = AlgDataTy ns (modifyContainedASTs f dcs)

