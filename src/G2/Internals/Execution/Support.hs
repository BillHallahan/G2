module G2.Internals.Execution.Support
    ( module G2.Internals.Execution.Support
    ) where

import G2.Internals.Language

import qualified Data.Map as M

data ExecState = ExecState { exec_stack :: Stack
                           , exec_scope :: Scope
                           , exec_code :: Code
                           , exec_names :: Renamer
                           , exec_paths :: [ExecCond]
                           } deriving (Show, Eq, Read)

fromState :: State -> ExecState
fromState = undefined

toState :: State -> ExecState -> State
toState = undefined

data Symbol = Symbol Id (Maybe (Expr, Scope)) deriving (Show, Eq, Read)

newtype Stack = Stack [Frame] deriving (Show, Eq, Read)

data Frame = CaseFrame Id [Alt] Scope
           | ApplyFrame Expr Scope
           | UpdateFrame Name
           deriving (Show, Eq, Read)

newtype Scope = Scope (M.Map Name (Either Name EnvObj))
             deriving (Show, Eq, Read)

data EnvObj = ExprObj Expr
            | SymObj Symbol
            | BLACKHOLE
            deriving (Show, Eq, Read)

data Code = Evaluate Expr
          | Return Expr
          deriving (Show, Eq, Read)

data ExecCond = ExecAltCond Expr (AltCon, [Id]) Bool Scope
              | ExecExtCond Expr Bool Scope
              deriving (Show, Eq, Read)

pushStack :: Frame -> Stack -> Stack
pushStack frame (Stack frames) = Stack (frame : frames)

popStack :: Stack -> Maybe (Frame, Stack)
popStack (Stack []) = Nothing
popStack (Stack (frame:frames)) = Just (frame, Stack frames)

lookupScope :: Name -> Scope -> Maybe EnvObj
lookupScope name (Scope smap) = case M.lookup name smap of
    Just (Left redir) -> lookupScope redir (Scope smap)
    Just (Right eobj) -> Just eobj
    Nothing -> Nothing

vlookupScope :: Id -> Scope -> Maybe EnvObj
vlookupScope var scope = lookupScope (idName var) scope

insertEnvObj :: (Name, EnvObj) -> Scope -> Scope
insertEnvObj (k, v) (Scope smap) = Scope (M.insert k (Right v) smap)

insertEnvObjList :: [(Name, EnvObj)] -> Scope -> Scope
insertEnvObjList kvs scope = foldr insertEnvObj scope kvs

