module G2.Internals.Initialization.TyBinderInit (tyBinderInit) where

import G2.Internals.Language.Naming
import G2.Internals.Language.Syntax
import G2.Internals.Language.Support

import qualified Data.Map as M

tyBinderInit :: TypeEnv -> NameGen -> (TypeEnv, NameGen)
tyBinderInit tenv ng = 
    let
        (tenv', ng') = tyBinderTypeEnv' (M.toList tenv) ng
    in
    (M.fromList tenv', ng')

tyBinderTypeEnv' :: [(Name, AlgDataTy)] -> NameGen -> ([(Name, AlgDataTy)], NameGen)
tyBinderTypeEnv' [] ng = ([], ng)
tyBinderTypeEnv' ((n, DataTyCon _ dc):ts) ng =
    let
        (ns, dc', ng') = modifyDC ng dc
        (ts', ng'') = tyBinderTypeEnv' ts ng'
    in
    ((n, DataTyCon ns dc'):ts', ng'')
tyBinderTypeEnv' ((n, NewTyCon _ dc rt):ts) ng =
    let
        (ns, [dc'], ng') = modifyDC ng [dc]
        (ts', ng'') = tyBinderTypeEnv' ts ng'
    in
    ((n, NewTyCon ns dc' rt):ts', ng'')

modifyDC :: NameGen -> [DataCon] -> ([Name], [DataCon], NameGen)
modifyDC ng dc = 
    let
        num = case dc of
            (d:_) -> dcForAllNum d
            _ -> 0

        (ns, ng') = freshSeededNames (replicate num (Name "t" Nothing 0)) ng

        dc' = map (dcReplaceNames ns) dc
    in
    (ns, dc', ng')

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