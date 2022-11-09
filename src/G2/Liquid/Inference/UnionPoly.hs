{-# LANGUAGE BangPatterns #-}

module G2.Liquid.Inference.UnionPoly () where

import G2.Language

import qualified Data.Map as M

data FuncPos = FuncPos Name -- ^ The function name
                       ArgOrRet -- ^ The position in the function type
                       [Int] -- ^ Position in the argument/return

data ArgOrRet = Arg Int
              | Ret

-- The position in the argument refers to
-- (1) an additional argument count, in the case of a higher order function
-- (2) a path through ADT constructors

sharedTyCons :: Expr
             -> M.Map Name FuncPos -- TyVar names to positions in functions that correspond to those TyVars
sharedTyCons e@(App _ _) | Var (Id n t):as <- unApp e = stcExprType 0 n t as

stcExprType :: Int -> Name -> Type -> [Expr] -> M.Map Name FuncPos
stcExprType !k func_name (TyForAll _ t) (Type _:es) = stcExprType k func_name t es
stcExprType !k func_name (TyFun t1 t2) (e:es) =
    stcTypeType 0 (Arg k) [] func_name t1 (typeOf e) `M.union` stcExprType (k + 1) func_name t2 es
stcExprType !k func_name t [e] = stcTypeType 0 Ret [] func_name t (typeOf e)

stcTypeType :: Int -> ArgOrRet -> [Int] -> Name -> Type -> Type -> M.Map Name FuncPos
stcTypeType k ar pos func_name (TyVar (Id n _)) _ = M.singleton n (FuncPos func_name ar $ reverse pos)
stcTypeType !k ar pos func_name (TyFun t1 t2) (TyFun t1' t2') =
    stcTypeType 0 ar (k:pos) func_name t1 t1' `M.union` stcTypeType (k + 1) ar pos func_name t2 t2'
stcTypeType !k ar pos func_name (TyApp t1 t2) (TyApp t1' t2') =
    stcTypeType 0 ar (k:pos) func_name t1 t1' `M.union` stcTypeType (k + 1) ar pos func_name t2 t2'
