{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}

module G2.Liquid.Inference.PolyRef (extractPolyBound) where

import G2.Language

import qualified Data.HashMap.Lazy as HM
import Data.List
import Data.Maybe
import Debug.Trace

import Debug.Trace

-- | The subexpressions of an expression corresponding to the polymorphic
-- arguments.  If a polymorphic argument is instantiated with a polymorphic
-- type, these are nested recursively.
data PolyBound = PolyBound [Expr] [PolyBound] deriving (Read, Show)

extractPolyBound :: Expr -> [PolyBound]
extractPolyBound e
    | Data dc:_ <- unApp e =
        let
            bound = leadingTyForAllBindings dc
            m = extractPolyBound' e

            bound_es = map (\i -> HM.lookupDefault [] i m) bound
        in
        map (\es -> PolyBound es (mergePolyBound . transpose $ map extractPolyBound es)) bound_es
    | otherwise = []

mergePolyBound :: [[PolyBound]] -> [PolyBound]
mergePolyBound = mapMaybe (\pb -> case pb of
                                (p:pbb) -> Just $ foldr mergePolyBound' p pbb
                                [] -> Nothing)

mergePolyBound' :: PolyBound -> PolyBound -> PolyBound
mergePolyBound' (PolyBound es1 pb1) (PolyBound es2 pb2) =
    PolyBound (es1 ++ es2) (map (uncurry mergePolyBound') $ zip pb1 pb2)

extractPolyBound' :: Expr -> HM.HashMap Id [Expr]
extractPolyBound' e
    | Data dc:es <- unApp e =
    let
        es' = filter (not . isType) es

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
substTypes _ e = e

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