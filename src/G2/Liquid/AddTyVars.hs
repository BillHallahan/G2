{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module G2.Liquid.AddTyVars ( addTyVarsEEnvTEnv
                           , addTyVarsMeasures

                           , PhantomTyVars) where

import G2.Initialization.Types
import G2.Language hiding (State (..), Bindings (..))
import qualified G2.Language.KnownValues as KV
import G2.Liquid.Types

import qualified Data.HashMap.Lazy as HM
import Data.List
import qualified Data.Map as M
import Data.Maybe
import Data.Text as T (pack)

import Debug.Trace

addTyVarsEEnvTEnv :: SimpleState -> (SimpleState, PhantomTyVars)
addTyVarsEEnvTEnv s@(SimpleState { expr_env = eenv
                                 , type_env = tenv
                                 , known_values = kv
                                 , name_gen = ng }) =
    let
        (new_mjn, ng') = mkNewMaybe kv ng

        unused_poly = getUnusedPoly tenv

        eenv' = addTyVarsExpr unused_poly new_mjn eenv
        tenv' = addTyVarsTypeEnv unused_poly new_mjn tenv

        tenv'' = addNewMaybe new_mjn tenv'
    in
    (s { expr_env = eenv', type_env = tenv'', name_gen = ng' }
       , PhantomTyVars { ph_new_maybe = new_mjn, ph_unused_poly = unused_poly })

addTyVarsMeasures :: PhantomTyVars -> LHStateM ()
addTyVarsMeasures PhantomTyVars { ph_new_maybe = new_mb, ph_unused_poly = unused_poly } = do
    meenv <- measuresM
    kv <- knownValues
    tenv <- typeEnv
    putMeasuresM (addTyVarsExpr unused_poly new_mb meenv)

-- | Identifies data constructors with unused polymorphic arguments
getUnusedPoly :: TypeEnv -> UnusedPoly 
getUnusedPoly tenv =
    let
        adts = M.elems tenv
    in
    foldr unionUP emptyUP $ map getUnusedPoly' adts

getUnusedPoly' :: AlgDataTy -> UnusedPoly
getUnusedPoly' adt =
    let
        bound = bound_ids adt
        dcs = case adt of
                DataTyCon { data_cons = dcs' } -> dcs'
                NewTyCon {} -> []
                TypeSynonym {} -> []
    in
    foldr (uncurry insertUP) emptyUP $ mapMaybe (getUnusedPoly'' bound) dcs

getUnusedPoly'' :: [Id] -> DataCon -> Maybe (Name, [Int])
getUnusedPoly'' is dc@(DataCon n _) =
    let
        used = tyVarIds . argumentTypes . PresType . inTyForAlls $ typeOf dc
    in
    case filter (flip notElem used) is of
        [] -> Nothing
        not_used -> Just (n, getTypeInds not_used (typeOf dc))

getTypeInds :: [Id] -> Type -> [Int]
getTypeInds is t =
    map fst
        . filter (flip elem is . snd)
        . zip [0..]
        . leadingTyForAllBindings
        $ PresType t

-------------------------------
-- Adjust TypeEnv
-------------------------------
addTyVarsTypeEnv :: UnusedPoly -> NewMaybe -> TypeEnv -> TypeEnv
addTyVarsTypeEnv unused new_mb = M.map (addTyVarADT unused new_mb) 

addTyVarADT :: UnusedPoly -> NewMaybe -> AlgDataTy -> AlgDataTy
addTyVarADT unused new_mb dtc@(DataTyCon { data_cons = dcs }) =
    dtc { data_cons = map (addTyVarDC unused new_mb) dcs }
addTyVarADT _ _ adt = adt

addNewMaybe :: NewMaybe -> TypeEnv -> TypeEnv
addNewMaybe new_mb@(NewMaybe { new_maybe = new_mb_t }) tenv =
    let
        dtc = DataTyCon { bound_ids = [Id (new_maybe_bound new_mb) TYPE]
                        , data_cons = [mkNewJustDC new_mb, mkNewNothingDC new_mb] }
    in
    M.insert new_mb_t dtc tenv

-------------------------------
-- Adjust Expr
-------------------------------
addTyVarsExpr :: ASTContainer m Expr => UnusedPoly -> NewMaybe -> m -> m
addTyVarsExpr unused new_mb =
    modifyASTs (addTyVarsExprCase unused new_mb) . addTyVarsExprDC unused new_mb

addTyVarsExprDC :: ASTContainer m Expr => UnusedPoly -> NewMaybe -> m -> m
addTyVarsExprDC unused new_mb = modifyAppTop (addTyVarsExprDC' unused new_mb)

addTyVarsExprDC' :: UnusedPoly -> NewMaybe -> Expr -> Expr
addTyVarsExprDC' unused new_mb e
    | Data dc@(DataCon n _):ars <- unApp e
    , Just is <- lookupUP n unused =
        let
            (ty_ars, expr_ars) = partition (isTypeExpr) ars

            bnds = map (\(Type t, i) -> Id (Name "bind_for_sym" Nothing i Nothing) t) $ zip ars is
            sym_gens = map (\(Type t) -> SymGen t) $ map (ars !!) is
            let_e = Let (zip bnds sym_gens) 
            -- nothings = map (\(Type t) -> mkNewNothing new_mb) $ map (ars !!) is
        in
        let_e . mkApp $ Data (addTyVarDC unused new_mb dc):ty_ars ++ map Var bnds ++ expr_ars
    | otherwise = e

addTyVarsExprCase :: UnusedPoly -> NewMaybe -> Expr -> Expr
addTyVarsExprCase unused new_mb (Case e i as) =
    Case e i $ map (addTyVarsAlt unused new_mb e) as
addTyVarsExprCase _ _ e = e

addTyVarsAlt :: UnusedPoly -> NewMaybe -> Expr -> Alt -> Alt
addTyVarsAlt unused new_mb case_e alt@(Alt (DataAlt dc@(DataCon n t) is) alt_e)
    | Just i <- lookupUP n unused = 
        let
            dc' = addTyVarDC unused new_mb dc

            ty_binds = reverse . unTyApp $ typeOf case_e

            n_str = "a_FILLING_IN_HERE"
            new_is = map (\(n, tyi) -> Id (Name (T.pack $ n_str ++ show n) Nothing 0 Nothing) $ tyi) 
                   . zip [0..]
                   $ map (ty_binds !!) i
            is' = new_is ++ is
        in
        Alt (DataAlt dc' is') alt_e
addTyVarsAlt _ _ _ alt = alt

-------------------------------
-- Generic
-------------------------------
addTyVarDC :: UnusedPoly -> NewMaybe -> DataCon -> DataCon
addTyVarDC unused new_mb dc@(DataCon n t)
    | Just is <- lookupUP n unused = DataCon n (addTyVarsToType new_mb is t)
    | otherwise = dc

addTyVarsToType :: NewMaybe -> [Int] -> Type -> Type
addTyVarsToType new_mb i t =
    let
        ty_binds = leadingTyForAllBindings (PresType t)
        is = map (ty_binds !!) i
    in
    mapInTyForAlls (\t' -> mkTyFun $ map TyVar is ++ [t']) t

isTypeExpr :: Expr -> Bool
isTypeExpr (Type _) = True
isTypeExpr _ = False

-------------------------------
-- Added TyVar
-------------------------------

data PhantomTyVars = PhantomTyVars { ph_new_maybe :: NewMaybe, ph_unused_poly :: UnusedPoly }

-------------------------------
-- New Maybe
-------------------------------
data NewMaybe = NewMaybe { new_maybe :: Name

                         , new_maybe_bound :: Name
                         , new_just :: Name
                         , new_nothing :: Name }

mkNewMaybe :: KnownValues -> NameGen -> (NewMaybe, NameGen)
mkNewMaybe kv ng =
    let
        ((n_m, n_j, n_n), ng') = renameAll ( Name "NewMaybe" Nothing 0 Nothing
                                           , Name "NewJust" Nothing 0 Nothing
                                           , Name "NewNothing" Nothing 0 Nothing) ng
        bnd = Name "a_NEW_MAYBE" Nothing 0 Nothing
    in
    (NewMaybe { new_maybe = n_m, new_maybe_bound = bnd, new_just = n_j, new_nothing = n_n }, ng')

mkNewMaybeTy :: NewMaybe -> Type
mkNewMaybeTy new_mb = TyCon (new_maybe new_mb) (TyFun TYPE TYPE)

mkNewJust :: NewMaybe -> Expr
mkNewJust = Data . mkNewJustDC

mkNewJustDC :: NewMaybe -> DataCon
mkNewJustDC new_mb =
    let
        n = new_just new_mb

        a = new_maybe_bound new_mb
        tya = TyVar (Id a TYPE)
        t = TyForAll (NamedTyBndr (Id a TYPE))
          . TyFun tya
          $ TyApp (TyCon (new_maybe new_mb) TYPE) tya
    in
    DataCon n t


mkNewNothing :: NewMaybe -> Expr
mkNewNothing = Data . mkNewNothingDC

mkNewNothingDC :: NewMaybe -> DataCon
mkNewNothingDC new_mb =
    let
        n = new_nothing new_mb

        a = new_maybe_bound new_mb
        tya = TyVar (Id a TYPE)
        t = TyForAll (NamedTyBndr (Id a TYPE))
          $ TyApp (TyCon (new_maybe new_mb) TYPE) tya
    in
    DataCon n t

-------------------------------
-- UnusedPoly
-------------------------------
newtype UnusedPoly = UnusedPoly (HM.HashMap Name [Int])
                     deriving (Show, Read)

emptyUP :: UnusedPoly
emptyUP = UnusedPoly HM.empty

lookupUP :: Name -> UnusedPoly -> Maybe [Int]
lookupUP n (UnusedPoly up) = HM.lookup n up

insertUP :: Name -> [Int] -> UnusedPoly -> UnusedPoly
insertUP n is (UnusedPoly up) = UnusedPoly $ HM.insert n is up

unionUP :: UnusedPoly -> UnusedPoly -> UnusedPoly
unionUP (UnusedPoly up1) (UnusedPoly up2) = UnusedPoly $ HM.union up1 up2