{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module G2.Internals.Language.TypeEnv where

import G2.Internals.Language.AST
import G2.Internals.Language.Naming
import G2.Internals.Language.Syntax

import qualified Data.Map as M
import Data.Maybe

-- | Type environments map names of types to their appropriate types. However
-- our primary interest with these is for dealing with algebraic data types,
-- and we only store those information accordingly.
type TypeEnv = M.Map Name AlgDataTy

-- Returns a list of all argument function types in the type env
argTypesTEnv :: TypeEnv -> [Type]
argTypesTEnv = concatMap (evalASTs argTypesTEnv') . M.elems

argTypesTEnv' :: Type -> [Type]
argTypesTEnv' t@(TyFun _ _) = [t]
argTypesTEnv' _ = []

-- | Algebraic data types are types constructed with parametrization of some
-- names over types, and a list of data constructors for said type.
data AlgDataTy = AlgDataTy [Name] [DataCon] deriving (Show, Eq, Read)

isPolyAlgDataTy :: AlgDataTy -> Bool
isPolyAlgDataTy (AlgDataTy ns _) = not $ null ns

getDataCons :: Name -> TypeEnv -> Maybe [DataCon]
getDataCons n tenv =
    case M.lookup n tenv of
        Just (AlgDataTy _ dc) -> Just dc
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
    
dataConWithName :: AlgDataTy -> Name -> Maybe DataCon
dataConWithName (AlgDataTy _ dcs) n = listToMaybe $ filter (flip dataConHasName n) dcs

dataConHasName :: DataCon -> Name -> Bool
dataConHasName (DataCon n _ _) n' = n == n'
dataConHasName _ _ = False

instance ASTContainer AlgDataTy Expr where
    containedASTs _ = []
    modifyContainedASTs _ a = a

instance ASTContainer AlgDataTy Type where
    containedASTs (AlgDataTy _ dcs) = containedASTs dcs
    modifyContainedASTs f (AlgDataTy ns dcs) = AlgDataTy ns (modifyContainedASTs f dcs)

instance ASTContainer AlgDataTy DataCon where
    containedASTs (AlgDataTy _ dcs) = dcs

    modifyContainedASTs f (AlgDataTy ns dcs) = AlgDataTy ns (modifyContainedASTs f dcs)

instance Named AlgDataTy where
    names (AlgDataTy _ dc) = names dc

    rename old new (AlgDataTy n dc) = AlgDataTy (rename old new n) (rename old new dc)