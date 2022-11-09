{-# LANGUAGE BangPatterns, DeriveGeneric #-}

module G2.Liquid.Inference.UnionPoly (sharedTyConsEE) where

import G2.Language
import qualified G2.Language.ExprEnv as E

import GHC.Generics (Generic)
import Data.Hashable
import qualified Data.HashMap.Lazy as HM

data FuncPos = FuncPos Name -- ^ The function name
                       ArgOrRet -- ^ The position in the function type
                       [Int] -- ^ Position in the argument/return
               deriving (Eq, Generic)

instance Hashable FuncPos

data ArgOrRet = Arg Int
              | Ret
              deriving (Eq, Generic)

instance Hashable ArgOrRet

-- The position in the argument refers to
-- (1) an additional argument count, in the case of a higher order function
-- (2) a path through ADT constructors

sharedTyConsEE :: [Name] -> ExprEnv -> HM.HashMap FuncPos Name
sharedTyConsEE ns = foldr HM.union HM.empty . E.map' sharedTyCons . E.filterWithKey (\n _ -> n `elem` ns)

sharedTyCons :: Expr
             -> HM.HashMap FuncPos Name -- Positions in functions to correspond TyVar Names
sharedTyCons e@(App _ _) | Var (Id n t):as <- unApp e = stcExprType 0 n t as

stcExprType :: Int -> Name -> Type -> [Expr] -> HM.HashMap FuncPos Name
stcExprType !k func_name (TyForAll _ t) (Type _:es) = stcExprType k func_name t es
stcExprType !k func_name (TyFun t1 t2) (e:es) =
    stcTypeType 0 (Arg k) [] func_name t1 (typeOf e) `HM.union` stcExprType (k + 1) func_name t2 es
stcExprType !k func_name t [e] = stcTypeType 0 Ret [] func_name t (typeOf e)

stcTypeType :: Int -> ArgOrRet -> [Int] -> Name -> Type -> Type -> HM.HashMap FuncPos Name
stcTypeType k ar pos func_name (TyVar (Id n _)) _ = HM.singleton (FuncPos func_name ar $ reverse pos) n
stcTypeType !k ar pos func_name (TyFun t1 t2) (TyFun t1' t2') =
    stcTypeType 0 ar (k:pos) func_name t1 t1' `HM.union` stcTypeType (k + 1) ar pos func_name t2 t2'
stcTypeType !k ar pos func_name (TyApp t1 t2) (TyApp t1' t2') =
    stcTypeType 0 ar (k:pos) func_name t1 t1' `HM.union` stcTypeType (k + 1) ar pos func_name t2 t2'
