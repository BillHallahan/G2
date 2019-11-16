{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}

module G2.Liquid.Inference.PolyRef ( PolyBound (.. )
                                   , RefNamePolyBound
                                   , ExprPolyBound
                                   , extractExprPolyBoundWithRoot
                                   , extractExprPolyBound
                                   , extractTypePolyBoundPresFull
                                   , extractTypePolyBound

                                   , extractValues
                                   , uniqueIds
                                   , mapPB
                                   , zipPB
                                   , zip3PB) where

import G2.Language

import qualified Data.HashMap.Lazy as HM
import Data.List
import Data.Maybe
import Debug.Trace

type RefNamePolyBound = PolyBound String
type ExprPolyBound = PolyBound [Expr]

type TypePolyBound = PolyBound Type

-- | The subexpressions of an expression corresponding to the polymorphic
-- arguments.  If a polymorphic argument is instantiated with a polymorphic
-- type, these are nested recursively.
data PolyBound v = PolyBound v [PolyBound v] deriving (Eq, Read, Show)

-------------------------------
-- ExprPolyBound
-------------------------------

extractExprPolyBoundWithRoot :: Expr -> ExprPolyBound
extractExprPolyBoundWithRoot e = PolyBound [e] $ extractExprPolyBound e

extractExprPolyBound :: Expr -> [ExprPolyBound]
extractExprPolyBound e
    | Data dc:_ <- unApp e =
        let
            bound = leadingTyForAllBindings dc
            m = extractExprPolyBound' e

            bound_es = map (\i -> HM.lookupDefault [] i m) bound
        in
        map (\es -> PolyBound es (mergeExprPolyBound . transpose $ map extractExprPolyBound es)) bound_es
    | otherwise = []

mergeExprPolyBound :: [[ExprPolyBound]] -> [ExprPolyBound]
mergeExprPolyBound = mapMaybe (\pb -> case pb of
                                (p:pbb) -> Just $ foldr mergeExprPolyBound' p pbb
                                [] -> Nothing)

mergeExprPolyBound' :: ExprPolyBound -> ExprPolyBound -> ExprPolyBound
mergeExprPolyBound' (PolyBound es1 pb1) (PolyBound es2 pb2) =
    PolyBound (es1 ++ es2) (map (uncurry mergeExprPolyBound') $ zip pb1 pb2)

extractExprPolyBound' :: Expr -> HM.HashMap Id [Expr]
extractExprPolyBound' e
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
    foldr (HM.unionWith (++)) direct_hm $ map (extractExprPolyBound' . adjustIndirectTypes) indirect'
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


-------------------------------
-- TypePolyBound
-------------------------------

-- | Unrolls TyApp'ed args, while also keeping them in the base type
extractTypePolyBoundPresFull :: Type -> TypePolyBound
extractTypePolyBoundPresFull t =
    let
        (t':ts) = unTyApp t
    in
    PolyBound t $ map extractTypePolyBound ts

extractTypePolyBound :: Type -> TypePolyBound
extractTypePolyBound t =
    let
        (t':ts) = unTyApp t
    in
    PolyBound t' $ map extractTypePolyBound ts

-------------------------------
-- Generic PolyBound functions
-------------------------------

extractValues :: PolyBound v -> [v]
extractValues (PolyBound v ps) = v:concatMap extractValues ps

uniqueIds :: PolyBound v -> PolyBound Int
uniqueIds = snd . uniqueIds' 0 

uniqueIds' :: Int -> PolyBound v -> (Int, PolyBound Int)
uniqueIds' n (PolyBound _ ps) =
    let
        (n', ps') = mapAccumR (uniqueIds') (n + 1) ps
    in
    (n', PolyBound n ps')

mapPB :: (a -> b) -> PolyBound a -> PolyBound b
mapPB f (PolyBound v ps) = PolyBound (f v) (map (mapPB f) ps)

zipPB :: PolyBound a -> PolyBound b -> PolyBound (a, b)
zipPB (PolyBound a pba) (PolyBound b pbb) = PolyBound (a, b) (zipWith zipPB pba pbb)

zip3PB :: PolyBound a -> PolyBound b -> PolyBound c -> PolyBound (a, b, c)
zip3PB (PolyBound a pba) (PolyBound b pbb) (PolyBound c pbc) =
    PolyBound (a, b, c) (zipWith3 zip3PB pba pbb pbc)
