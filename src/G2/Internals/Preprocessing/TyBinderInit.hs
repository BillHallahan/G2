module G2.Internals.Preprocessing.TyBinderInit (tyBinderInit) where

import G2.Internals.Language.Naming
import G2.Internals.Language.Syntax
import G2.Internals.Language.Support

import qualified Data.Map as M

tyBinderInit :: State -> State
tyBinderInit s@State {type_env = tenv, name_gen = ng} =
    let
        (tenv', ng') = tyBinderTypeEnv tenv ng
    in
    s {type_env = tenv', name_gen = ng'}

tyBinderTypeEnv :: TypeEnv -> NameGen -> (TypeEnv, NameGen)
tyBinderTypeEnv tenv ng = 
    let
        (tenv', ng') = tyBinderTypeEnv' (M.toList tenv) ng
    in
    (M.fromList tenv', ng')

tyBinderTypeEnv' :: [(Name, AlgDataTy)] -> NameGen -> ([(Name, AlgDataTy)], NameGen)
tyBinderTypeEnv' [] ng = ([], ng)
tyBinderTypeEnv' ((n, AlgDataTy _ dc):ts) ng =
    let
        num = case dc of
            (d:_) -> dcForAllNum d
            _ -> 0

        (ns, ng') = freshSeededNames (replicate num (Name "t" Nothing 0)) ng

        dc' = map (dcReplaceNames ns) dc

        (ts', ng'') = tyBinderTypeEnv' ts ng'
    in
    ((n, AlgDataTy ns dc'):ts', ng'')

dcForAllNum :: DataCon -> Int
dcForAllNum (DataCon _ t _ ) = tyForAllNum t
dcForAllNum _ = 0

tyForAllNum :: Type -> Int
tyForAllNum (TyForAll _ ts) = 1 + tyForAllNum ts
tyForAllNum _ = 0

dcReplaceNames :: [Name] -> DataCon -> DataCon
dcReplaceNames ns dc =
    let
        ns' = dcForAllNames dc

        nss = zip ns' ns
    in
    foldr (uncurry rename) dc nss

dcForAllNames :: DataCon -> [Name]
dcForAllNames (DataCon _ t _) = tyForAllNames t
dcForAllNames _ = []

tyForAllNames :: Type -> [Name]
tyForAllNames (TyForAll (NamedTyBndr (Id n _)) ts) = n:tyForAllNames ts
tyForAllNames _ = []