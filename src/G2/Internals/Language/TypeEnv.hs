{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module G2.Internals.Language.TypeEnv where

import G2.Internals.Language.AST
import G2.Internals.Language.Syntax

import qualified Data.Map as M
import Data.Maybe

type ProgramType = (Name, AlgDataTy)

-- | Type environments map names of types to their appropriate types. However
-- our primary interest with these is for dealing with algebraic data types,
-- and we only store those information accordingly.
type TypeEnv = M.Map Name AlgDataTy

-- | Algebraic data types are types constructed with parametrization of some
-- names over types, and a list of data constructors for said type.
data AlgDataTy = DataTyCon { bound_names :: [Name]
                           , data_cons :: [DataCon] }
               | NewTyCon { bound_name :: [Name]
                          , data_con :: DataCon
                          , rep_type :: Type } deriving (Show, Eq, Read)


-- Returns a list of all argument function types in the type env
argTypesTEnv :: TypeEnv -> [Type]
argTypesTEnv = concatMap (evalASTs argTypesTEnv') . M.elems

argTypesTEnv' :: Type -> [Type]
argTypesTEnv' t@(TyFun _ _) = [t]
argTypesTEnv' _ = []

dataCon :: AlgDataTy -> [DataCon]
dataCon (DataTyCon {data_cons = dc}) = dc
dataCon (NewTyCon {data_con = dc}) = [dc]

isPolyAlgDataTy :: AlgDataTy -> Bool
isPolyAlgDataTy = not . null . bound_names

getDataCons :: Name -> TypeEnv -> Maybe [DataCon]
getDataCons n tenv =
    case M.lookup n tenv of
        Just (DataTyCon _ dc) -> Just dc
        Just (NewTyCon _ dc _) -> Just [dc]
        Nothing -> Nothing

baseDataCons :: [DataCon] -> [DataCon]
baseDataCons = filter baseDataCon

baseDataCon :: DataCon -> Bool
baseDataCon (DataCon _ _ (_:_)) = False
baseDataCon _ = True

getDataCon :: TypeEnv -> Name -> Name -> Maybe DataCon
getDataCon tenv adt dc =
    let
        adt' = M.lookup adt tenv
    in
    maybe Nothing (flip dataConWithName dc) adt'

dataConArgs :: DataCon -> [Type]
dataConArgs (DataCon _ _ ts) = ts
dataConArgs _ = []

dataConWithName :: AlgDataTy -> Name -> Maybe DataCon
dataConWithName (DataTyCon _ dcs) n = listToMaybe $ filter (flip dataConHasName n) dcs
dataConWithName _ _ = Nothing

dataConHasName :: DataCon -> Name -> Bool
dataConHasName (DataCon n _ _) n' = n == n'
dataConHasName _ _ = False

instance ASTContainer AlgDataTy Expr where
    containedASTs _ = []

    modifyContainedASTs _ a = a

instance ASTContainer AlgDataTy Type where
    containedASTs (DataTyCon _ dcs) = containedASTs dcs
    containedASTs (NewTyCon _ dcs r) = containedASTs dcs ++ containedASTs r

    modifyContainedASTs f (DataTyCon ns dcs) = DataTyCon ns (modifyContainedASTs f dcs)
    modifyContainedASTs f (NewTyCon ns dcs rt) = NewTyCon ns (modifyContainedASTs f dcs) (modifyContainedASTs f rt)

instance ASTContainer AlgDataTy DataCon where
    containedASTs (DataTyCon _ dcs) = dcs
    containedASTs (NewTyCon _ dcs _) = [dcs]

    modifyContainedASTs f (DataTyCon ns dcs) = DataTyCon ns (modifyContainedASTs f dcs)
    modifyContainedASTs f (NewTyCon ns dc rt) = NewTyCon ns (modifyContainedASTs f dc) rt