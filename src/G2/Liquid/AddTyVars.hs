{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module G2.Liquid.AddTyVars ( addTyVarsEEnvTEnv
                           , addTyVarsMeasures

                           , PhantomTyVars) where

import G2.Initialization.Types
import G2.Language hiding (State (..), Bindings (..))
import G2.Liquid.Types

import qualified Data.HashMap.Lazy as HM
import Data.List
import Data.Maybe
import Data.Text as T (pack)
import qualified G2.Language.TyVarEnv as TV 

addTyVarsEEnvTEnv :: TV.TyVarEnv -> SimpleState -> (SimpleState, PhantomTyVars)
addTyVarsEEnvTEnv tv s@(SimpleState { expr_env = eenv
                                 , type_env = tenv
                                 , known_values = kv
                                 , name_gen = ng }) =
    let
        (new_mjn, ng') = mkNewMaybe kv ng

        unused_poly = getUnusedPoly tv tenv

        eenv' = addTyVarsExpr tv unused_poly eenv ng eenv
        tenv' = addTyVarsTypeEnv tv unused_poly tenv

        tenv'' = addNewMaybe new_mjn tenv'
    in
    (s { expr_env = eenv', type_env = tenv'', name_gen = ng' }
       , PhantomTyVars { ph_new_maybe = new_mjn, ph_unused_poly = unused_poly })

addTyVarsMeasures :: TV.TyVarEnv -> PhantomTyVars -> LHStateM ()
addTyVarsMeasures tv PhantomTyVars { ph_unused_poly = unused_poly } = do
    meenv <- measuresM
    ng <- nameGen
    putMeasuresM (addTyVarsExpr tv unused_poly meenv ng meenv)

-- | Identifies data constructors with unused polymorphic arguments
getUnusedPoly :: TV.TyVarEnv -> TypeEnv -> UnusedPoly 
getUnusedPoly tv tenv =
    let
        adts = HM.elems tenv
    in
    foldr unionUP emptyUP $ map (getUnusedPoly' tv) adts

getUnusedPoly' :: TV.TyVarEnv -> AlgDataTy -> UnusedPoly
getUnusedPoly' tv adt =
    let
        bound = bound_ids adt
        dcs = case adt of
                DataTyCon { data_cons = dcs' } -> dcs'
                NewTyCon {} -> []
                TypeSynonym {} -> []
    in
    foldr (uncurry insertUP) emptyUP $ mapMaybe (getUnusedPoly'' tv bound) dcs

getUnusedPoly'' :: TV.TyVarEnv -> [Id] -> DataCon -> Maybe (Name, [Int])
getUnusedPoly'' tv is dc@(DataCon n _ _ _) =
    let
        used = tyVarIds . argumentTypes . inTyForAlls $ typeOf tv dc
    in
    case filter (flip notElem used) is of
        [] -> Nothing
        not_used -> Just (n, getTypeInds not_used (typeOf tv dc))

getTypeInds :: [Id] -> Type -> [Int]
getTypeInds is t =
    map fst
        . filter (flip elem is . snd)
        . zip [0..]
        . leadingTyForAllBindings $ t

-------------------------------
-- Adjust TypeEnv
-------------------------------
addTyVarsTypeEnv :: TV.TyVarEnv -> UnusedPoly -> TypeEnv -> TypeEnv
addTyVarsTypeEnv tv unused = HM.map (addTyVarADT tv unused) 

addTyVarADT :: TV.TyVarEnv -> UnusedPoly -> AlgDataTy -> AlgDataTy
addTyVarADT tv unused dtc@(DataTyCon { data_cons = dcs }) =
    dtc { data_cons = map (addTyVarDC unused) dcs }
addTyVarADT _ _ adt = adt

addNewMaybe :: NewMaybe -> TypeEnv -> TypeEnv
addNewMaybe new_mb@(NewMaybe { new_maybe = new_mb_t }) tenv =
    let
        dtc = DataTyCon { bound_ids = [Id (new_maybe_bound new_mb) TYPE]
                        , data_cons = [mkNewJustDC new_mb, mkNewNothingDC new_mb] }
    in
    HM.insert new_mb_t dtc tenv

-------------------------------
-- Adjust Expr
-------------------------------

addTyVarsExpr :: ASTContainer m Expr => TV.TyVarEnv -> UnusedPoly -> ExprEnv -> NameGen -> m -> m
addTyVarsExpr tv unused eenv ng =
    modifyASTs (addTyVarsExprCase tv unused) . addTyVarsExprDC unused . etaExpandDC tv eenv ng

etaExpandDC :: ASTContainer m Expr => TV.TyVarEnv -> ExprEnv -> NameGen -> m -> m
etaExpandDC tv eenv ng = modifyAppedDatas (etaExpandDC' tv eenv ng) 

etaExpandDC' :: TV.TyVarEnv -> ExprEnv -> NameGen -> DataCon -> [Expr] -> Expr
etaExpandDC' tv eenv ng dc ars =
    let
        e = mkApp (Data dc:ars)
        num_binds = length $ leadingTyForAllBindings (typeOf tv dc)
        (e', _) = etaExpandTo tv eenv ng num_binds e
    in
    e'

addTyVarsExprDC :: ASTContainer m Expr => UnusedPoly -> m -> m
addTyVarsExprDC unused = modifyAppedDatas (addTyVarsExprDC' unused)

addTyVarsExprDC' :: UnusedPoly -> DataCon -> [Expr] -> Expr
addTyVarsExprDC' unused dc@(DataCon n _ _ _) ars
    | Just is <- lookupUP n unused =
        let
            (ty_ars, expr_ars) = partition (isTypeExpr) ars

            sym_gens = map (\(Type t) -> SymGen SNoLog t) $ map (ars !!) is
            -- nothings = map (\(Type t) -> mkNewNothing new_mb) $ map (ars !!) is
        in
        mkApp $ Data (addTyVarDC unused dc):ty_ars ++ sym_gens ++ expr_ars
    | otherwise = mkApp $ Data dc:ars

addTyVarsExprCase :: TV.TyVarEnv -> UnusedPoly -> Expr -> Expr
addTyVarsExprCase tv unused (Case e i t as) =
    Case e i t $ map (addTyVarsAlt tv unused e) as
addTyVarsExprCase _ _ e = e

addTyVarsAlt :: TV.TyVarEnv -> UnusedPoly -> Expr -> Alt -> Alt
addTyVarsAlt tv unused case_e (Alt (DataAlt dc@(DataCon n _ _ _) is) alt_e)
    | Just i <- lookupUP n unused = 
        let
            dc' = addTyVarDC unused dc

            ty_binds = reverse . unTyApp $ typeOf tv case_e

            n_str = "a_FILLING_IN_HERE"
            new_is = map (\(l, tyi) -> Id (Name (T.pack $ n_str ++ show l) Nothing 0 Nothing) $ tyi) 
                   . zip ([0..] :: [Int])
                   $ map (ty_binds !!) i
            is' = new_is ++ is
        in
        Alt (DataAlt dc' is') alt_e
addTyVarsAlt _ _ _ alt = alt

-------------------------------
-- Generic
-------------------------------
addTyVarDC :: UnusedPoly -> DataCon -> DataCon
addTyVarDC unused dc@(DataCon n t u e)
    | Just is <- lookupUP n unused = DataCon n (addTyVarsToType is t) u e
    | otherwise = dc

addTyVarsToType :: [Int] -> Type -> Type
addTyVarsToType i t =
    let
        ty_binds = leadingTyForAllBindings t
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
mkNewMaybe _ ng =
    let
        ((n_m, n_j, n_n), ng') = renameAll ( Name "NewMaybe" Nothing 0 Nothing
                                           , Name "NewJust" Nothing 0 Nothing
                                           , Name "NewNothing" Nothing 0 Nothing) ng
        bnd = Name "a_NEW_MAYBE" Nothing 0 Nothing
    in
    (NewMaybe { new_maybe = n_m, new_maybe_bound = bnd, new_just = n_j, new_nothing = n_n }, ng')

mkNewJustDC :: NewMaybe -> DataCon
mkNewJustDC new_mb =
    let
        n = new_just new_mb

        a = new_maybe_bound new_mb
        tya = TyVar (Id a TYPE)
        t = TyForAll (Id a TYPE)
          . TyFun tya
          $ TyApp (TyCon (new_maybe new_mb) TYPE) tya
    in
    DataCon n t [Id a TYPE] []

mkNewNothingDC :: NewMaybe -> DataCon
mkNewNothingDC new_mb =
    let
        n = new_nothing new_mb

        a = new_maybe_bound new_mb
        tya = TyVar (Id a TYPE)
        t = TyForAll (Id a TYPE)
          $ TyApp (TyCon (new_maybe new_mb) TYPE) tya
    in
    DataCon n t [Id a TYPE] []

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