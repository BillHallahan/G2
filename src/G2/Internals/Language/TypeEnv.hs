{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module G2.Internals.Language.TypeEnv ( ProgramType
                                     , TypeEnv
                                     , AlgDataTy (..)
                                     , nameModMatch
                                     , argTypesTEnv
                                     , dataCon
                                     , isPolyAlgDataTy
                                     , isDataTyCon
                                     , isNewTyCon
                                     , newTyConRepType
                                     , getDataCons
                                     , baseDataCons
                                     , getCastedAlgDataTy
                                     , getCasted
                                     , selfRecursive
                                     , dataConCanContain
                                     , getDataCon
                                     , getDataConNameMod
                                     , getDataConNameMod'
                                     , dataConArgs
                                     , dcName
                                     , retypeAlgDataTy) where

import G2.Internals.Language.AST
import G2.Internals.Language.Syntax
import G2.Internals.Language.Typing

import Data.List
import qualified Data.Map as M
import Data.Maybe

import Debug.Trace

type ProgramType = (Name, AlgDataTy)

-- | Type environments map names of types to their appropriate types. However
-- our primary interest with these is for dealing with algebraic data types,
-- and we only store those information accordingly.
type TypeEnv = M.Map Name AlgDataTy

-- | Algebraic data types are types constructed with parametrization of some
-- names over types, and a list of data constructors for said type.
data AlgDataTy = DataTyCon { bound_names :: [Name]
                           , data_cons :: [DataCon] }
               | NewTyCon { bound_names :: [Name]
                          , data_con :: DataCon
                          , rep_type :: Type } deriving (Show, Eq, Read)

nameModMatch :: Name -> TypeEnv -> Maybe Name
nameModMatch (Name n m _) = find (\(Name n' m' _) -> n == n' && m == m' ) . M.keys

-- Returns a list of all argument function types in the type env
argTypesTEnv :: TypeEnv -> [Type]
argTypesTEnv = concatMap (evalASTs argTypesTEnv') . M.elems

argTypesTEnv' :: Type -> [Type]
argTypesTEnv' t@(TyFun _ _) = [t]
argTypesTEnv' _ = []

dataCon :: AlgDataTy -> [DataCon]
dataCon (DataTyCon {data_cons = dc}) = dc
dataCon (NewTyCon {data_con = dc}) = [dc]

dcName :: DataCon -> Name
dcName (DataCon n _ _) = n

isPolyAlgDataTy :: AlgDataTy -> Bool
isPolyAlgDataTy = not . null . bound_names

isDataTyCon :: AlgDataTy -> Bool
isDataTyCon (DataTyCon {}) = True
isDataTyCon _ = False

isNewTyCon :: AlgDataTy -> Bool
isNewTyCon (NewTyCon {}) = True
isNewTyCon _ = False

newTyConRepType :: AlgDataTy -> Maybe Type
newTyConRepType (NewTyCon {rep_type = t}) = Just t
newTyConRepType _ = Nothing

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

getCastedAlgDataTy :: Name -> TypeEnv -> Maybe AlgDataTy
getCastedAlgDataTy n tenv =
    case M.lookup n tenv of
        Just (NewTyCon {rep_type = TyConApp n' _}) -> getCastedAlgDataTy n' tenv
        Just (NewTyCon {}) -> Nothing
        dc@(Just (DataTyCon {})) -> dc
        _ -> Nothing

getCasted :: Name -> TypeEnv -> Maybe Type
getCasted n tenv =
    case M.lookup n tenv of
        Just (NewTyCon {rep_type = TyConApp n' _}) -> getCasted n' tenv
        Just (NewTyCon {rep_type = t}) -> Just t
        Just (DataTyCon {bound_names = bn}) -> Just $ TyConApp n (map (\n' -> TyVar (Id n' TYPE)) bn)
        _ -> Nothing

-- | selfRecursive
-- Given a DataCon dc of type t, checks if one of the descendents of dc could
-- be of type t
selfRecursive :: TypeEnv -> DataCon -> Bool
selfRecursive tenv dc =
    let
        tydc = typeOf dc
        ts = dataConCanContain tenv dc
    in
    tydc `elem` ts

-- | dataConCanContain
-- Recursively searches the possible contents of a DataCon, to determine all
-- the types that could be anywhere below it in an AST
dataConCanContain :: TypeEnv -> DataCon -> [Type]
dataConCanContain tenv = nub . dataConCanContain' tenv

dataConCanContain' :: TypeEnv -> DataCon -> [Type]
dataConCanContain' tenv (DataCon _ _ ts) =
    let
        pt = filter (not . isAlgDataTy) $ ts
        dcs = filter isAlgDataTy $ ts

        adts = concat . mapMaybe (fmap dataCon . flip M.lookup tenv . tyConAppName) $ dcs

        recT = concatMap (dataConCanContain tenv) adts
    in
    pt ++ (map typeOf dcs) ++ recT
dataConCanContain' _ _ = []

tyConAppName :: Type -> Name
tyConAppName (TyConApp n _) = n
tyConAppName _ = error "tyConAppName: Type other than TyConApp"

getDataCon :: TypeEnv -> Name -> Name -> Maybe DataCon
getDataCon tenv adt dc =
    let
        adt' = M.lookup adt tenv
    in
    maybe Nothing (flip dataConWithName dc) adt'

getDataConNameMod :: TypeEnv -> Name -> Name -> Maybe DataCon
getDataConNameMod tenv (Name n m _) dc =
    let
        adt' = fmap snd $ find (\(Name n' m' _, _) -> n == n' && m == m') $ M.toList tenv
    in
    trace ("n = " ++ n ++ " m = " ++ show m ++ "\nadt' = " ++ show adt') maybe Nothing (flip dataConWithNameMod dc) adt'

getDataConNameMod' :: TypeEnv -> Name -> Maybe DataCon
getDataConNameMod' tenv n = find (flip dataConHasNameMod n) $ concatMap dataCon $ M.elems tenv

dataConArgs :: DataCon -> [Type]
dataConArgs (DataCon _ _ ts) = ts
dataConArgs _ = []

dataConWithName :: AlgDataTy -> Name -> Maybe DataCon
dataConWithName (DataTyCon _ dcs) n = listToMaybe $ filter (flip dataConHasName n) dcs
dataConWithName _ _ = Nothing

dataConHasName :: DataCon -> Name -> Bool
dataConHasName (DataCon n _ _) n' = n == n'
dataConHasName _ _ = False

dataConWithNameMod :: AlgDataTy -> Name -> Maybe DataCon
dataConWithNameMod (DataTyCon _ dcs) n = listToMaybe $ filter (flip dataConHasNameMod n) dcs
dataConWithNameMod _ _ = Nothing

dataConHasNameMod :: DataCon -> Name -> Bool
dataConHasNameMod (DataCon (Name n m _) _ _) (Name n' m' _) = n == n' && m == m'
dataConHasNameMod _ _ = False

retypeAlgDataTy :: [Type] -> AlgDataTy -> AlgDataTy
retypeAlgDataTy ts adt =
    let
        ns = map (flip Id TYPE) $ bound_names adt
    in
    foldr (uncurry retype) adt $ zip ns ts

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
