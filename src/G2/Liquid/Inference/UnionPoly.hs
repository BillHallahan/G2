{-# LANGUAGE BangPatterns, DeriveGeneric, OverloadedStrings #-}

module G2.Liquid.Inference.UnionPoly (sharedTyConsEE) where

import G2.Language
import qualified G2.Language.ExprEnv as E
import G2.Language.Monad.AST
import G2.Language.Monad.Naming
import G2.Language.Monad.Support

import GHC.Generics (Generic)
import Data.Hashable
import qualified Data.HashMap.Lazy as HM

import Debug.Trace
import G2.Language.Monad (freshNameN)

data FuncPos = FuncPos Name -- ^ The function name
                       ArgOrRet -- ^ The position in the function type
                       [Int] -- ^ Position in the argument/return
               deriving (Eq, Show, Generic)

instance Hashable FuncPos

data ArgOrRet = Arg Int
              | Ret
              deriving (Eq, Show, Generic)

instance Hashable ArgOrRet

-- The position in the argument refers to
-- (1) an additional argument count, in the case of a higher order function
-- (2) a path through ADT constructors

sharedTyConsEE :: [Name] -> ExprEnv -> HM.HashMap Name Type -- HM.HashMap FuncPos Name
sharedTyConsEE ns eenv =
    let
        f_eenv = E.filterWithKey (\n _ -> n `elem` ns) eenv
        tys = fst $ runNamingM (mapM assignTyConNames (E.map' typeOf f_eenv)) (mkNameGen f_eenv)

        rep_eenv = E.map (repVars tys) f_eenv

        union_poly = E.map' checkType rep_eenv 
    in
    trace ("tys = " ++ show tys ++ "\nrep_eenv = " ++ show rep_eenv ++ "\nunion_poly = " ++ show union_poly) tys -- foldr HM.union HM.empty . E.map' sharedTyCons $ f_eenv

assignTyConNames :: Type -> NameGenM Type
assignTyConNames = modifyASTsM assignTyConNames'

assignTyConNames' :: Type -> NameGenM Type
assignTyConNames' (TyCon _ k) = do
    n <- freshSeededStringN "__G2__UNION__NAME__"
    return (TyVar (Id n k))
assignTyConNames' t = return t 

repVars :: HM.HashMap Name Type -> Expr -> Expr
repVars tys = modifyASTs (repVars' tys)
 
repVars' :: HM.HashMap Name Type -> Expr -> Expr
repVars' tys (Var (Id n _)) | Just t <- HM.lookup n tys = Var (Id n t)
repVars' _ e = e

sharedTyCons :: Expr
             -> HM.HashMap FuncPos Name -- Positions in functions to correspond TyVar Names
sharedTyCons e@(App _ _) | Var (Id n t):as <- unApp e =
    let hm = stcExprType 0 n t as in
    case HM.null hm of
        False -> trace ("sharedTyCons'\ne = " ++ show e ++ "\nhm = " ++ show hm) hm <> HM.unions (map sharedTyCons as)
        True -> hm
sharedTyCons e = evalChildren sharedTyCons e

stcExprType :: Int -> Name -> Type -> [Expr] -> HM.HashMap FuncPos Name
stcExprType !k func_name (TyForAll _ t) (Type _:es) = stcExprType k func_name t es
stcExprType !k func_name (TyFun t1 t2) (e:es) =
    stcTypeType 0 (Arg k) [] func_name t1 (typeOf e) `HM.union` stcExprType (k + 1) func_name t2 es
stcExprType !k func_name t [e] = stcTypeType 0 Ret [] func_name t (typeOf e)
stcExprType _ _ _ _ = HM.empty

stcTypeType :: Int -> ArgOrRet -> [Int] -> Name -> Type -> Type -> HM.HashMap FuncPos Name
stcTypeType k ar pos func_name (TyVar (Id n _)) _ =
    HM.singleton (FuncPos func_name ar $ reverse pos) n
stcTypeType !k ar pos func_name (TyFun t1 t2) (TyFun t1' t2') =
    stcTypeType 0 ar (k:pos) func_name t1 t1' `HM.union` stcTypeType (k + 1) ar pos func_name t2 t2'
stcTypeType !k ar pos func_name (TyApp t1 t2) (TyApp t1' t2') =
    stcTypeType 0 ar (k:pos) func_name t1 t1' `HM.union` stcTypeType (k + 1) ar pos func_name t2 t2'
stcTypeType _ _ _ _ _ _ = HM.empty
