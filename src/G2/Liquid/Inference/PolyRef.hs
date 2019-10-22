{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}

module G2.Liquid.Inference.PolyRef (extractPolyBound) where

import G2.Language

import qualified Data.HashMap.Lazy as HM
import Data.List
import Data.Maybe
import Debug.Trace

import Debug.Trace

extractPolyBound :: Expr -> HM.HashMap Id [Expr]
extractPolyBound e = extractPolyBound' e

extractPolyBound' :: Expr -> HM.HashMap Id [Expr]
extractPolyBound' e
    | Data dc:es <- unApp e =
    let
        (tyses, es') = partition (isType) es
        tyses' = map (\(Type t) -> t) tyses

        bound = leadingTyForAllBindings dc
        bound_tyses = zip bound tyses'
        argtys = argumentTypes . PresType . inTyForAlls $ typeOf dc

        argtys_es = zip argtys es'

        (direct, indirect) = partition fstIsTyVar argtys_es
        direct' =  mapMaybe fstMapTyVar direct
        indirect' = map (uncurry substTypes) indirect

        direct_hm = foldr (HM.unionWith (++)) HM.empty
                        $ map (\(i, e) -> uncurry HM.singleton (i, e:[])) direct'
    in
    foldr (HM.unionWith (++)) direct_hm $ map (extractPolyBound' . adjustIndirectTypes) indirect'
    | otherwise = HM.empty
    where
        isType (Type _) = True
        isType _ = False

        fstIsTyVar (TyVar _, _) = True
        fstIsTyVar _ = False

        fstMapTyVar (TyVar i, x) = Just (i, x)
        fstMapTyVar _ = Nothing

substTypes :: Type -> Expr -> Expr
substTypes t e
    | t':ts <- unTyApp t
    , e':es <- unApp e =
        mkApp $ e':substTypes' ts es

substTypes' :: [Type] -> [Expr] -> [Expr]
substTypes' (t:ts) (Type _:es) = Type t:substTypes' ts es
substTypes' _ es = es

adjustIndirectTypes :: Expr -> Expr
adjustIndirectTypes e
    | Data dc:es <- unApp e =
        let
            (tyses, es') = partition (isType) es
            tyses' = map (\(Type t) -> t) tyses

            bound = leadingTyForAllBindings dc
            bound_tyses = zip bound tyses'
        in
        mkApp $ Data (foldr (uncurry retype) dc $ bound_tyses):es
    | otherwise = e
    where
        isType (Type _) = True
        isType _ = False
