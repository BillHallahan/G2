module G2.Internals.Language.Support
    ( module G2.Internals.Language.Support
    ) where

import G2.Internals.Language.Syntax

import qualified Data.Map as M

data State = State { expr_env :: !ExprEnv
                   , type_env :: !TypeEnv
                   , stack :: !Stack
                   , curr_expr :: !Expr
                   , all_names :: ![Name]
                   , path_conds :: ![PathCond]
                   , sym_links :: !SymLinks
                   , fun_table :: !FuncInterps
                   } deriving (Show, Eq, Read)

data Symbol = Symbol Id (Maybe (Expr, ExprEnv)) deriving (Show, Eq, Read)

type ExprEnv = M.Map Name (Either Name EnvObj)

data EnvObj = ValObj Expr
            | FunObj Id Expr ExprEnv
            | ConObj DataCon [Expr] ExprEnv
            | ThunkObj Expr ExprEnv
            | SymObj Symbol
            | BLACKHOLE
            deriving (Show, Eq, Read)

type TypeEnv = M.Map Name (Either Name Type)

newtype Stack = Stack [Frame] deriving (Show, Eq, Read)

data Frame = CaseFrame  Id [Alt] Expr ExprEnv
           | ApplyFrame Expr ExprEnv
           | UpdateFrame Name
           deriving (Show, Eq, Read)

data PathCond = AltCond Expr (AltCon, [Id]) Bool ExprEnv
              | ExtCond Expr Bool ExprEnv
              deriving (Show, Eq, Read)

newtype SymLinks = SymLinks (M.Map Name (Name, Type, Maybe Int))
                 deriving (Show, Eq, Read)

newtype FuncInterps = FuncInterps (M.Map Name (Name, Interp))
                    deriving (Show, Eq, Read)

data Interp = StdInt | UnInt deriving (Show, Eq, Read)

idName :: Id -> Name
idName (Id name _) = name

pushStack :: Frame -> Stack -> Stack
pushStack frame (Stack frames) = Stack (frame : frames)

popStack :: Stack -> Maybe (Frame, Stack)
popStack (Stack []) = Nothing
popStack (Stack (frame:frames)) = Just (frame, Stack frames)

lookupExprEnv :: Name -> ExprEnv -> Maybe EnvObj
lookupExprEnv name eenv = case M.lookup name eenv of
    Just (Left redir) -> lookupExprEnv redir eenv
    Just (Right eobj) -> Just eobj
    Nothing -> Nothing

vlookupExprEnv :: Id -> ExprEnv -> Maybe EnvObj
vlookupExprEnv var eenv = lookupExprEnv (idName var) eenv

insertEnvObj :: (Name, EnvObj) -> ExprEnv -> ExprEnv
insertEnvObj (name, eobj) eenv = M.insert name (Right eobj) eenv

insertEnvObjList :: [(Name, EnvObj)] -> ExprEnv -> ExprEnv
insertEnvObjList kvs eenv = foldr insertEnvObj eenv kvs

-- vlookupExpr :: Id -> ExprEnv -> Maybe Expr
-- vlookupExpr (Id name _) eenv = lookupExpr name eenv

lookupType :: Name -> TypeEnv -> Maybe Type
lookupType name tenv = case M.lookup name tenv of
    Just (Left redir) -> lookupType redir tenv
    Just (Right ty) -> Just ty
    Nothing -> Nothing

lookupSymLinks :: Name -> SymLinks -> Maybe (Name, Type, Maybe Int)
lookupSymLinks name (SymLinks smap) = M.lookup name smap

insertSymLinks :: Name -> (Name, Type, Maybe Int) -> SymLinks -> SymLinks
insertSymLinks new old (SymLinks smap) = SymLinks (M.insert new old smap)

lookupFuncInterps :: Name -> FuncInterps -> Maybe (Name, Interp)
lookupFuncInterps name (FuncInterps fs) = M.lookup name fs

insertFuncInterps :: Name -> (Name, Interp) -> FuncInterps -> FuncInterps
insertFuncInterps fun int (FuncInterps fs) = FuncInterps (M.insert fun int fs)

