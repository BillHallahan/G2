{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module G2.Liquid.AddTyVars ( addTyVarsEEnvTEnv
                           , addTyVarsMeasures

                           , UnusedPoly
                           , emptyUP) where

import G2.Initialization.Types
import G2.Language hiding (State (..))
import G2.Liquid.Types

import qualified Data.HashMap.Lazy as HM
import Data.List
import qualified Data.Map as M
import Data.Maybe

addTyVarsEEnvTEnv :: SimpleState -> (SimpleState, UnusedPoly)
addTyVarsEEnvTEnv s@(SimpleState { expr_env = eenv, type_env = tenv}) =
    let
        unused_poly = getUnusedPoly tenv

        eenv' = addTyVarsExpr unused_poly eenv
        tenv' = addTyVarsTypeEnv unused_poly tenv
    in
    (s { expr_env = eenv', type_env = tenv' }, unused_poly)

addTyVarsMeasures :: UnusedPoly -> LHStateM ()
addTyVarsMeasures unused_poly = do
    meenv <- measuresM
    putMeasuresM (addTyVarsExpr unused_poly meenv)

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
addTyVarsTypeEnv :: UnusedPoly -> TypeEnv -> TypeEnv
addTyVarsTypeEnv unused = M.map (addTyVarADT unused) 

addTyVarADT :: UnusedPoly -> AlgDataTy -> AlgDataTy
addTyVarADT unused dtc@(DataTyCon { data_cons = dcs }) =
    dtc { data_cons = map (addTyVarDC unused) dcs }
addTyVarADT _ adt = adt

-------------------------------
-- Adjust Expr
-------------------------------
addTyVarsExpr :: ASTContainer m Expr => UnusedPoly -> m -> m
addTyVarsExpr unused =
    modifyASTs (addTyVarsExprCase unused) . modifyAppTop (addTyVarsExprDC unused)

addTyVarsExprDC :: UnusedPoly -> Expr -> Expr
addTyVarsExprDC unused e
    | Data dc@(DataCon n _):ars <- unApp e
    , Just is <- lookupUP n unused =
        let
            (ty_ars, expr_ars) = partition (isTypeExpr) ars

            sym_gens = map (\(Type t) -> SymGen t) $ map (ars !!) is
        in
        mkApp $ Data (addTyVarDC unused dc):ty_ars ++ sym_gens ++ expr_ars
    | otherwise = e
    where
        isTypeExpr (Type _) = True
        isTypeExpr _ = False

addTyVarsExprCase :: UnusedPoly -> Expr -> Expr
addTyVarsExprCase unused (Case e i as) =
    Case e i $ map (addTyVarsAlt unused) as
addTyVarsExprCase _ e = e

addTyVarsAlt :: UnusedPoly -> Alt -> Alt
addTyVarsAlt unused alt@(Alt (DataAlt dc@(DataCon n t) is) e)
    | Just i <- lookupUP n unused = 
        let
            dc' = addTyVarDC unused dc

            ty_binds = leadingTyForAllBindings dc
            new_is = map (ty_binds !!) i
            is' = new_is ++ is
        in
        Alt (DataAlt dc' is') e
addTyVarsAlt _ alt = alt

-------------------------------
-- Generic
-------------------------------
addTyVarDC :: UnusedPoly -> DataCon -> DataCon
addTyVarDC unused dc@(DataCon n t)
    | Just is <- lookupUP n unused = DataCon n (addTyVarsToType is t)
    | otherwise = dc

addTyVarsToType :: [Int] -> Type -> Type
addTyVarsToType i t =
    let
        ty_binds = leadingTyForAllBindings (PresType t)
        is = map (ty_binds !!) i
    in
    mapInTyForAlls (\t' -> mkTyFun $ map TyVar is ++ [t']) t

-------------------------------
-- PolyUnused
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