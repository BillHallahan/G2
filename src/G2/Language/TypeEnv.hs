{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module G2.Language.TypeEnv
  ( TypeEnv
  
  , nameModMatch
  , argTypesTEnv
  , getDataCons
  , getCastedAlgDataTy
  , getAlgDataTy
  , getDataCon
  , getDataConNameMod
  , module G2.Language.AlgDataTy
  ) where

import G2.Language.AST
import G2.Language.Syntax
import G2.Language.Typing
import G2.Language.AlgDataTy

import Data.List
import qualified Data.HashMap.Lazy as M

-- | The type environment maps names of types to their appropriate types. However
-- our primary interest with these is for dealing with algebraic data types,
-- and we only store those information accordingly.
type TypeEnv = M.HashMap Name AlgDataTy

nameModMatch :: Name -> TypeEnv -> Maybe Name
nameModMatch (Name n m _ _) = find (\(Name n' m' _ _) -> n == n' && m == m' ) . M.keys

-- | Returns a list of all argument function types in the `TypeEnv`
argTypesTEnv :: TypeEnv -> [Type]
argTypesTEnv = concatMap (evalASTs argTypesTEnv') . M.elems

argTypesTEnv' :: Type -> [Type]
argTypesTEnv' (TyFun t@(TyFun _ _) _) = [t]
argTypesTEnv' _ = []

getDataCons :: Name -> TypeEnv -> Maybe [DataCon]
getDataCons n tenv = dataCon <$> M.lookup n tenv

-- | If the Type is a TyCon, (optionally) wrapped with TyApps,
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
getDataCon tenv adt dc = flip dataConWithName dc =<< M.lookup adt tenv

getDataConNameMod :: TypeEnv -> Name -> Name -> Maybe DataCon
getDataConNameMod tenv (Name n m _ _) dc =
    let
        adt' = fmap snd $ find (\(Name n' m' _ _, _) -> n == n' && m == m') $ M.toList tenv
    in
    flip dataConWithNameMod dc =<< adt'

dataConWithNameMod :: AlgDataTy -> Name -> Maybe DataCon
dataConWithNameMod (DataTyCon _ dcs _) n = find (`dataConHasNameMod` n) dcs
dataConWithNameMod _ _ = Nothing

dataConHasNameMod :: DataCon -> Name -> Bool
dataConHasNameMod (DataCon (Name n m _ _) _) (Name n' m' _ _) = n == n' && m == m'