{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module G2.Language.TypeEnv
  ( TypeEnv
  
  , nameModMatch
  , argTypesTEnv
  , dataCon
  , boundIds
  , isPolyAlgDataTy
  , isDataTyCon
  , isNewTyCon
  , newTyConRepType
  , typeStripCastType
  , getDataCons
  , baseDataCons
  , getCastedAlgDataTy
  , getAlgDataTy
  , getDataCon
  , dataConsFromADT
  , getDataConNoType
  , getTypeNameMod
  , getDataConNameMod
  , getDataConNameMod'
  , dataConArgs
  , dataConWithName
  , dcName
  , retypeAlgDataTy
  , module G2.Language.AlgDataTy
  ) where

import G2.Language.AST
import G2.Language.Syntax
import G2.Language.Typing
import G2.Language.AlgDataTy

import Data.List
import qualified Data.Map as M
import Data.Maybe

-- | The type environment maps names of types to their appropriate types. However
-- our primary interest with these is for dealing with algebraic data types,
-- and we only store those information accordingly.
type TypeEnv = M.Map Name AlgDataTy

nameModMatch :: Name -> TypeEnv -> Maybe Name
nameModMatch (Name n m _ _) = find (\(Name n' m' _ _) -> n == n' && m == m' ) . M.keys

-- Returns a list of all argument function types in the type env
argTypesTEnv :: TypeEnv -> [Type]
argTypesTEnv = concatMap (evalASTs argTypesTEnv') . M.elems

argTypesTEnv' :: Type -> [Type]
argTypesTEnv' (TyFun t@(TyFun _ _) _) = [t]
argTypesTEnv' _ = []

dataCon :: AlgDataTy -> [DataCon]
dataCon (DataTyCon {data_cons = dc}) = dc
dataCon (NewTyCon {data_con = dc}) = [dc]
dataCon (TypeSynonym {}) = []

boundIds :: AlgDataTy -> [Id]
boundIds = bound_ids

dcName :: DataCon -> Name
dcName (DataCon n _) = n

isPolyAlgDataTy :: AlgDataTy -> Bool
isPolyAlgDataTy = not . null . bound_ids

isDataTyCon :: AlgDataTy -> Bool
isDataTyCon (DataTyCon {}) = True
isDataTyCon _ = False

isNewTyCon :: AlgDataTy -> Bool
isNewTyCon (NewTyCon {}) = True
isNewTyCon _ = False

newTyConRepType :: AlgDataTy -> Maybe Type
newTyConRepType (NewTyCon {rep_type = t}) = Just t
newTyConRepType _ = Nothing

typeStripCastType :: TypeEnv -> Type -> Type
typeStripCastType tenv t
    | Just (adt, _) <- getCastedAlgDataTy t tenv
    , Just rt <- newTyConRepType adt =  rt
typeStripCastType _ t = t

getDataCons :: Name -> TypeEnv -> Maybe [DataCon]
getDataCons n tenv =
    case M.lookup n tenv of
        Just (DataTyCon _ dc) -> Just dc
        Just (NewTyCon _ dc _) -> Just [dc]
        Just (TypeSynonym _ (TyCon n' _)) -> getDataCons n' tenv
        _ -> Nothing

dataConsFromADT :: AlgDataTy -> [DataCon]
dataConsFromADT adt = case adt of
    DataTyCon _ _ -> data_cons adt
    NewTyCon _ _ _ -> [data_con adt]
    _ -> error "No DataCons"

baseDataCons :: [DataCon] -> [DataCon]
baseDataCons = filter baseDataCon

baseDataCon :: DataCon -> Bool
baseDataCon (DataCon _ t) = not $ hasTyFuns t

-- If the Type is a TyCon, (optionally) wrapped with TyApps,
-- returns the AlgDataTy of the Cast type, along with mappings from
-- the bound names of the cast type, to the types bound by the TyApps.
getCastedAlgDataTy :: Type -> TypeEnv -> Maybe (AlgDataTy, [(Id, Type)])
getCastedAlgDataTy t tenv
    | TyCon n _ <- tyAppCenter t
    , ts <- tyAppArgs t = getCastedAlgDataTy' n ts tenv
    | otherwise = Nothing

-- TODO : CHECK CORRECTNESS OF BOUND ARGS
getCastedAlgDataTy' :: Name -> [Type] -> TypeEnv -> Maybe (AlgDataTy, [(Id, Type)])
getCastedAlgDataTy' n ts tenv =
        case M.lookup n tenv of
            Just (NewTyCon {rep_type = TyCon n' _}) -> getCastedAlgDataTy' n' ts tenv
            Just (NewTyCon { }) -> Nothing
            (Just dc@(DataTyCon { bound_ids = bi })) -> Just (dc, zip bi ts)
            _ -> Nothing

getAlgDataTy :: Type -> TypeEnv -> Maybe (AlgDataTy, [(Id, Type)])
getAlgDataTy t tenv
    | TyCon n _ <- tyAppCenter t
    , ts <- tyAppArgs t = getAlgDataTy' n ts tenv
    | otherwise = Nothing

getAlgDataTy' :: Name -> [Type] -> TypeEnv -> Maybe (AlgDataTy, [(Id, Type)])
getAlgDataTy' n ts tenv =
        case M.lookup n tenv of
            Just dc@(NewTyCon {bound_ids = bi}) -> Just (dc, zip bi ts)
            Just dc@(DataTyCon { bound_ids = bi }) -> Just (dc, zip bi ts)
            _ -> Nothing

getDataCon :: TypeEnv -> Name -> Name -> Maybe DataCon
getDataCon tenv adt dc =
    let
        adt' = M.lookup adt tenv
    in
    maybe Nothing (flip dataConWithName dc) adt'

getDataConNoType :: TypeEnv -> Name -> Maybe DataCon
getDataConNoType tenv n = find (\dc -> dcName dc == n) . concatMap dataCon $ M.elems tenv

getTypeNameMod :: TypeEnv -> Name -> Maybe Name
getTypeNameMod tenv (Name n m _ _) = find (\(Name n' m' _ _) -> n == n' && m == m') $ M.keys tenv

getDataConNameMod :: TypeEnv -> Name -> Name -> Maybe DataCon
getDataConNameMod tenv (Name n m _ _) dc =
    let
        adt' = fmap snd $ find (\(Name n' m' _ _, _) -> n == n' && m == m') $ M.toList tenv
    in
    maybe Nothing (flip dataConWithNameMod dc) adt'

getDataConNameMod' :: TypeEnv -> Name -> Maybe DataCon
getDataConNameMod' tenv n = find (flip dataConHasNameMod n) $ concatMap dataCon $ M.elems tenv

dataConArgs :: DataCon -> [Type]
dataConArgs dc = anonArgumentTypes dc

dataConWithName :: AlgDataTy -> Name -> Maybe DataCon
dataConWithName (DataTyCon _ dcs) n = listToMaybe $ filter (flip dataConHasName n) dcs
dataConWithName _ _ = Nothing

dataConHasName :: DataCon -> Name -> Bool
dataConHasName (DataCon n _) n' = n == n'

dataConWithNameMod :: AlgDataTy -> Name -> Maybe DataCon
dataConWithNameMod (DataTyCon _ dcs) n = listToMaybe $ filter (flip dataConHasNameMod n) dcs
dataConWithNameMod _ _ = Nothing

dataConHasNameMod :: DataCon -> Name -> Bool
dataConHasNameMod (DataCon (Name n m _ _) _) (Name n' m' _ _) = n == n' && m == m'

retypeAlgDataTy :: [Type] -> AlgDataTy -> AlgDataTy
retypeAlgDataTy ts adt =
    foldr (uncurry retype) adt $ zip (bound_ids adt) ts
